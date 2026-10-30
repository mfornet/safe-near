#!/usr/bin/env python3
"""Build, verify and continuously publish the existing LeanArchitect/leanblueprint frontier."""
import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import html
import json
import os
import plistlib
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.request

from proof_sources import source_digest

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / 'contracts/w-near/verification'
WORK = PROJECT / '.lake/build/blueprint'
WEB = PROJECT / 'blueprint/web'
MANIFEST = PROJECT / 'blueprint/frontier.json'
DEFAULT_DEST = Path.home() / 'Library/Application Support/safe-near/blueprint'
DEFAULT_URL = 'https://obiteum-mac-studio.tail9c65ff.ts.net:8444/w-near/'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def utc():
    return datetime.now(timezone.utc).isoformat(timespec='seconds')


def atomic_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(path)


def run(args, cwd=PROJECT):
    print(f'{utc()}  {" ".join(map(str, args))}', flush=True)
    with (WORK / 'build.log').open('a') as log:
        result = subprocess.run(list(map(str, args)), cwd=cwd, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        tail = '\n'.join((WORK / 'build.log').read_text(errors='replace').splitlines()[-20:])
        raise RuntimeError(f'Command failed ({result.returncode}): {args}\n{tail}')


def snapshot():
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    digest = source_digest(ROOT)
    content = hashlib.sha256(digest.encode())
    for path in [MANIFEST, Path(__file__), ROOT / 'tools/proof_sources.py',
                 PROJECT / 'justfile', ROOT / 'notes/todo/wnear_refinement_status.md',
                 *sorted((PROJECT / 'blueprint/src').rglob('*'))]:
        if path.is_file() and (not path.is_relative_to(PROJECT / 'blueprint/src') or path.suffix in {'.tex', '.sty', '.css', '.cfg'} or path.name == 'latexmkrc'):
            content.update(str(path.relative_to(ROOT)).encode() + path.read_bytes())
    dirty = bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip())
    return {'revision': revision, 'dirty': dirty, 'proof_source_digest': digest, 'content_digest': content.hexdigest()}


def export_lean(manifest):
    names = ', '.join(json.dumps(n['declaration']) for n in manifest['nodes'])
    output = WORK / 'frontier-lean.json'
    source = '''import Blueprint
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command Meta
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let names : Array String := #[NAMES]
  let mut rows : Array Json := #[]
  for text in names do
    let name := text.toName
    let info ← getConstInfo name
    let (typeUsed, proofUsed) ← Architect.collectUsed name
    let axioms ← collectAxioms name
    let directSorry := (info.value? true).any fun value => value.getUsedConstants.contains ``sorryAx
    let some blueprintNode := Architect.blueprintExt.find? env name | throwError "missing blueprint annotation: {name}"
    let signature ← liftTermElabM <| PrettyPrinter.ppSignature name
    let shapeHash ← match info with
      | .defnInfo d => pure (mixHash d.type.hash d.value.hash)
      | .inductInfo i => do
        let mut h := i.type.hash
        for ctor in i.ctors do
          h := mixHash h (← getConstInfo ctor).type.hash
        pure h
      | _ => pure info.type.hash
    let statement ← match info with
      | .defnInfo d => liftTermElabM do
        let params ← forallTelescope d.type fun xs _ => xs.filterM fun x => do
          let n ← x.fvarId!.getUserName
          return !n.isAnonymous && !n.hasMacroScopes
        let body ← lambdaBoundedTelescope d.value params.size fun _ body => ppExpr body
        pure (s!"{signature.fmt} :=\n  {(Format.nest 2 body).pretty 98}")
      | _ => pure signature.fmt.pretty
    let module := (env.getModuleIdxFor? name).map fun i => env.header.moduleNames[i]!.toString
    rows := rows.push <| Json.mkObj [
      ("declaration", toJson text), ("module", toJson module),
      ("is_theorem", toJson info.isTheorem), ("direct_sorry", toJson directSorry),
      ("blueprint_label", toJson blueprintNode.latexLabel), ("not_ready", toJson blueprintNode.notReady),
      ("axioms", toJson (axioms.map Name.toString)),
      ("type_dependencies", toJson (typeUsed.toArray.map Name.toString)),
      ("proof_dependencies", toJson (proofUsed.toArray.map Name.toString)),
      ("statement", toJson statement), ("type_hash", toJson info.type.hash.toNat),
      ("shape_hash", toJson shapeHash.toNat)]
  let report := Json.mkObj [("nodes", Json.arr rows), ("exported_methods", toJson WNear.exportedMethods)]
  liftIO <| IO.FS.writeFile OUTPUT report.pretty
#eval do
  let wasm ← IO.FS.readBinFile "../contract.wasm"
  unless WNear.Binary.wNearBytes == wasm do
    throw (IO.userError "embedded binary differs from contract.wasm")
  let protocol ← IO.FS.readFile "../../../near-lean/vm/configs/runtime_config_v86.json"
  unless WNear.wNearProtocolJson == protocol do
    throw (IO.userError "embedded protocol differs from runtime_config_v86.json")
'''.replace('NAMES', names).replace('OUTPUT', json.dumps(str(output)))
    source_path = WORK / 'FrontierExport.lean'
    source_path.write_text(source)
    run(['lake', 'env', 'lean', source_path])
    payload = json.loads(output.read_text())
    actual = payload['exported_methods']
    declared = [n['method'] for n in manifest['nodes'] if 'method' in n]
    if len(actual) != len(set(actual)) or len(declared) != len(set(declared)) or set(actual) != set(declared):
        raise ValueError('Frontier methods do not exactly match the binary model exports')
    return payload['nodes']


def classify(manifest, rows, audit=None):
    indexed = {r['declaration']: r for r in rows}
    nodes = {n['declaration']: n for n in manifest['nodes']}
    if set(indexed) != set(nodes):
        raise ValueError('Missing or unexpected Lean declarations in the frontier export')
    contracts = {n['declaration'] for n in nodes.values() if n['kind'] == 'verification_contract'}
    direct = {r['declaration'] for r in rows if r['direct_sorry']}
    if direct != set(manifest['expected_admissions']):
        raise ValueError(f'Admission frontier changed: {sorted(direct ^ set(manifest["expected_admissions"]))}')
    result = []
    for name, node in nodes.items():
        row = indexed[name]
        if node.get('reviewed_shape_hash') != row.get('shape_hash'):
            raise ValueError(f'Unreviewed statement or contract change: {name}')
        if node['label'] != row.get('blueprint_label'):
            raise ValueError(f'LeanArchitect label mismatch: {name}')
        extra = set(row['axioms']) - STANDARD - {'sorryAx'}
        if extra:
            raise ValueError(f'Nonstandard axioms in {name}: {sorted(extra)}')
        if node['kind'] == 'verification_contract' or row['direct_sorry']:
            status = 'Open'
        elif not row['is_theorem']:
            raise ValueError(f'A definition cannot be presented as a proved theorem: {name}')
        elif 'sorryAx' in row['axioms'] or contracts.intersection(row['type_dependencies']):
            status = 'Conditional'
        else:
            status = 'Proven'
        typed = [nodes[n]['id'] for n in row['type_dependencies'] if n in nodes]
        proof = [nodes[n]['id'] for n in row['proof_dependencies'] if n in nodes]
        result.append({**node, **row, 'status': status, 'type_edges': typed,
                       'proof_edges': proof, 'integrated_into': []})
    by_id = {n['id']: n for n in result}
    for node in result:
        for dependency in node.get('required_instantiations', []):
            if dependency not in by_id:
                raise ValueError(f'Missing deployment-instantiation obligation: {dependency}')
            if by_id[dependency]['status'] != 'Proven' and node['status'] == 'Proven':
                node['status'] = 'Conditional'
        if node.get('not_ready') != (node['status'] != 'Proven'):
            raise ValueError(f'LeanArchitect readiness does not match {node["status"]} status: {node["declaration"]}')
    for caller in result:
        if caller['is_theorem'] and not caller['direct_sorry']:
            for dep in caller['proof_edges']:
                by_id[dep]['integrated_into'].append({'id': caller['id'], 'status': caller['status']})
    required = {'global': ['exported'], 'exported': ['dispatch', 'binary-size'] +
                [n['id'] for n in result if (n['kind'] == 'admission' and not n.get('indirect_admission')) or n.get('exported_direct')],
                'dispatch': [n['id'] for n in result if n.get('method') and n['kind'] != 'admission' and not n.get('exported_direct')]}
    for caller, deps in required.items():
        absent = set(deps) - set(by_id[caller]['proof_edges'])
        if absent:
            raise ValueError(f'Checked composition lost dependencies in {caller}: {sorted(absent)}')
    for node in result:
        missing_proof = set(node.get('required_proof_dependencies', [])) - set(node['proof_edges'])
        if missing_proof:
            raise ValueError(f'Checked composition lost dependencies in {node["id"]}: {sorted(missing_proof)}')
        absent = set(node.get('required_type_dependencies', [])) - set(node['type_edges'])
        if absent:
            raise ValueError(f'Expected verification hypotheses missing from {node["id"]}: {sorted(absent)}')
    if audit:
        actual = {r['declaration'] for r in audit['violations']}
        if actual != set(manifest['expected_incomplete']):
            raise ValueError(f'Untracked or stale audit frontier: {sorted(actual ^ set(manifest["expected_incomplete"]))}')
        for violation in audit['violations']:
            if set(violation['axioms']) - {'sorryAx'}:
                raise ValueError(f'Unapproved audit axiom: {violation}')
    return result


def render_frontier(data):
    colors = {'Proven': '#047857', 'Conditional': '#a16207', 'Open': '#be123c'}
    q = json.dumps
    dot = ['digraph frontier { graph [rankdir=LR,bgcolor="transparent"]; node [shape=box,style="rounded,filled",fontname="Helvetica",fontcolor=white];']
    for n in data['nodes']:
        dot.append(f'{q(n["id"])} [label={q(n["title"]+chr(10)+n["status"])},fillcolor={q(colors[n["status"]])},URL={q("frontier.html#"+n["id"])},target="_top"];')
        for dep in set(n['type_edges'] + n['proof_edges']):
            dot.append(f'{q(dep)} -> {q(n["id"])} [color="#475569"];')
        for dep in n.get('planned_dependencies', []):
            dot.append(f'{q(dep)} -> {q(n["id"])} [style=dashed,color="#94a3b8",label="planned"];')
    dot.append('}')
    (WORK / 'frontier.dot').write_text('\n'.join(dot))
    run(['dot', '-Tsvg', WORK / 'frontier.dot', '-o', WEB / 'frontier.svg'])
    cards = []
    for n in data['nodes']:
        callers = ', '.join(f'<a href="#{html.escape(c["id"])}">{html.escape(c["id"])} ({c["status"]})</a>' for c in n['integrated_into']) or 'No tracked caller composition yet'
        deps = ', '.join(f'<a href="#{html.escape(d)}">{html.escape(d)}</a>' for d in sorted(set(n['type_edges']+n['proof_edges']))) or 'No tracked dependencies'
        cards.append(f'''<article id="{n['id']}" data-status="{n['status']}" class="card {n['status']}">
<h2>{html.escape(n['title'])}</h2><strong>{n['status']}</strong>
<p><code>{html.escape(n['declaration'])}</code></p>
<p>{html.escape(n.get('notes', n.get('environment', '')))}</p>
<p>Checked dependencies: {deps}</p><p>Integrated into: {callers}</p>
<details><summary>Actual Lean statement and premises</summary><pre>{html.escape(n['statement'])}</pre></details>
<p class="small">Axioms: {html.escape(', '.join(n['axioms']) or 'none')}; type hash {n['type_hash']}</p></article>''')
    state = ' + uncommitted changes' if data['dirty'] else ' (clean checkout)'
    freshness = f'''Source revision <code>{data['revision']}</code>{state}<br>Last successful build: {data['built_at']}<br>
Proof source digest <code>{data['proof_source_digest']}</code><br>Full audit: {html.escape(data['audit_status'])}'''
    global_node = next(n for n in data['nodes'] if n['id'] == 'global')
    global_summary = 'complete' if global_node['status'] == 'Proven' else 'incomplete (' + global_node['status'] + ')'
    open_methods = ', '.join(n['title'] for n in data['nodes'] if n.get('method') and n['status'] != 'Proven') or 'none'
    open_protocol = ', '.join(n['title'] for n in data['nodes'] if n['id'].startswith('protocol-') and n['status'] == 'Open') or 'none'
    page = '''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>wNEAR dependency frontier</title><style>
body{font:16px/1.55 system-ui,sans-serif;background:#f8fafc;color:#172033;max-width:1500px;margin:auto;padding:28px}h1{margin-bottom:8px}a{color:#1d4ed8}code,pre{font-size:12px;overflow-wrap:anywhere}pre{white-space:pre-wrap}header,.legend{background:white;border:1px solid #cbd5e1;padding:22px;border-radius:12px;margin-bottom:20px}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(390px,1fr));gap:16px}.card{background:white;border:1px solid #cbd5e1;border-left:5px solid;padding:20px;border-radius:10px;scroll-margin-top:20px}.card h2{font-size:19px;margin-top:0}.Proven{border-left-color:#047857}.Conditional{border-left-color:#a16207}.Open{border-left-color:#be123c}.small{font-size:12px;color:#64748b}.graph{width:100%;height:75vh;overflow:auto;border:1px solid #cbd5e1;background:white}object{width:100%;height:75vh;min-width:100%;background:white}button{font:inherit;padding:7px 14px;margin:5px}#failure{color:#9f1239;font-weight:600}select,input{font:inherit;padding:8px;margin:8px}nav a{margin-right:20px}
</style><header><nav><a href="index.html">LeanArchitect / leanblueprint book</a><a href="frontier.json">Machine-readable evidence</a><a href="frontier.svg">Full dependency graph</a></nav>
<h1>wNEAR deployed-binary proof frontier</h1><p><b>The global refinement is GLOBAL_STATUS.</b> Status is derived from Lean declarations, axioms and named verification dependencies, not theorem counts.</p><p>FRESHNESS</p><p id="failure"></p></header>
<section class="legend"><b>Proven</b>: kernel checked under stated, reviewed environmental premises. <b>Conditional</b>: checked composition still assumes named verification obligations or depends on admitted leaves. <b>Open</b>: an exact contract exists but its proof is missing. <b>Integrated</b>: used in a tracked checked caller; a conditional caller remains incomplete. Definition check marks only establish a statement exists. Solid edges are actual LeanArchitect type/proof dependencies; dashed edges are planned and do not establish integration.
<p>The reviewed <code>Context.WF</code> premise includes uniqueness of staged/committed trie changes and assumes no witness hash is all zeros; it is not a cryptographic proof of SHA-256.</p>
<br><label>Filter <input id="search" placeholder="method, declaration or obligation"></label><select id="status"><option>All</option><option>Proven</option><option>Conditional</option><option>Open</option></select></section>
<div><button onclick="zoom(1.4)">Zoom in</button><button onclick="zoom(1/1.4)">Zoom out</button><button onclick="resetZoom()">Reset graph</button></div><div class="graph"><object id="graph" data="frontier.svg" type="image/svg+xml" aria-label="Proof dependency graph"></object></div><p>Incomplete methods: OPEN_METHODS. Open protocol obligations: OPEN_PROTOCOL. See the cards for remaining verification contracts and checked integration.</p><main class="grid">CARDS</main>
<script>let graphScale=1;function zoom(f){graphScale=Math.max(1,Math.min(8,graphScale*f));let g=document.querySelector("#graph");g.style.width=(graphScale*100)+"%";g.style.height=(graphScale*75)+"vh";}function resetZoom(){graphScale=1;zoom(1)}function filter(){const s=document.querySelector('#status').value,q=document.querySelector('#search').value.toLowerCase();document.querySelectorAll('article').forEach(n=>n.hidden=(s!=='All'&&n.dataset.status!==s)||!n.textContent.toLowerCase().includes(q));}document.querySelector('#search').oninput=filter;document.querySelector('#status').onchange=filter;
async function health(){try{const r=await fetch('../w-near-status.json',{cache:'no-store'});if(r.ok){const s=await r.json();document.querySelector('#failure').textContent=s.failure?'Build/serving failure: '+s.failure+' — displaying the last successful build.':'';}}catch(e){document.querySelector('#failure').textContent='Live build health unavailable; verify the build time above.';}}health();setInterval(health,15000);</script></html>'''
    (WEB / 'frontier.html').write_text(page.replace('FRESHNESS', freshness).replace('GLOBAL_STATUS', global_summary).replace('OPEN_METHODS', html.escape(open_methods)).replace('OPEN_PROTOCOL', html.escape(open_protocol)).replace('CARDS', ''.join(cards)))
    atomic_json(WEB / 'frontier.json', data)
    banner = f'<aside style="padding:18px;background:#fff7ed;border:2px solid #a16207"><b>Global refinement: {html.escape(global_node["status"])}.</b> <a href="frontier.html">Browse all methods, unresolved obligations and checked dependencies</a>. {freshness}</aside>'
    index = WEB / 'index.html'
    body = index.read_text()
    body, count = re.subn(r'(<body[^>]*>)', lambda m:m[1]+banner, body, count=1)
    if count != 1:
        raise ValueError('Rendered leanblueprint has no index body')
    index.write_text(body)


def publish(data, destination, url):
    destination.mkdir(parents=True, exist_ok=True)
    release = destination / ('w-near-release-' + str(time.time_ns()))
    shutil.copytree(WEB, release)
    live = destination / 'w-near'
    previous = live.readlink() if live.is_symlink() else None
    if live.exists() and not live.is_symlink():
        legacy = destination / ('w-near-legacy-' + str(time.time_ns()))
        live.rename(legacy)
        previous = Path(legacy.name)
    temporary = destination / 'w-near.next'
    temporary.unlink(missing_ok=True)
    temporary.symlink_to(release.name, target_is_directory=True)
    temporary.replace(live)
    try:
        # Verify the real stable tailnet URL and all rendered statuses/dependencies.
        with urllib.request.urlopen(url + 'frontier.json', timeout=30) as response:
            served = json.load(response)
        if served != data:
            raise RuntimeError('Served Lean frontier does not match the successful build')
        with urllib.request.urlopen(url, timeout=30) as response:
            if b'Browse all methods' not in response.read():
                raise RuntimeError('The stable blueprint URL does not show the frontier banner')
        with urllib.request.urlopen(url + 'frontier.html', timeout=30) as response:
            page = response.read().decode()
        if data['revision'] not in page or data['built_at'] not in page:
            raise RuntimeError('The served frontier does not show the current revision and build time')
        for node in data['nodes']:
            if f'id="{node["id"]}" data-status="{node["status"]}"' not in page:
                raise RuntimeError(f'Served status does not match Lean for {node["id"]}')
    except Exception:
        if previous is not None:
            temporary.unlink(missing_ok=True)
            temporary.symlink_to(previous, target_is_directory=True)
            temporary.replace(live)
        else:
            live.unlink(missing_ok=True)
        raise
    atomic_json(destination / 'w-near-status.json', {'failure': None, 'last_success': data['built_at'],
                'revision': data['revision'], 'proof_source_digest': data['proof_source_digest'], 'url': url})
    releases = sorted(destination.glob('w-near-release-*'), key=lambda p:p.stat().st_mtime)
    for old in releases[:-3]:
        shutil.rmtree(old)


def build(args):
    WORK.mkdir(parents=True, exist_ok=True)
    with (WORK / 'pipeline.lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        before = snapshot()
        evidence_path = WORK / 'audit-evidence.json'
        evidence = json.loads(evidence_path.read_text()) if evidence_path.exists() else {}
        audit_status = ('Passed for these Lean sources at '+evidence['checked_at']) if evidence.get('source_digest') == before['proof_source_digest'] else 'Pending for this source; selected frontier declarations checked, full strict audit not current'
        cached = WORK / 'last-success.json'
        if args.reuse and not args.audit_report and cached.exists() and (WEB / 'frontier.json').exists():
            data = json.loads(cached.read_text())
            if all(data.get(k) == v for k, v in before.items()) and data.get('audit_status') == audit_status:
                if args.publish:
                    publish(data, args.destination, args.url)
                print(json.dumps({'reused': True, 'built_at': data['built_at'], 'revision': data['revision'], 'url': args.url}), flush=True)
                return
        (WORK / 'build.log').write_text('')
        manifest = json.loads(MANIFEST.read_text())
        run(['lake', 'build', 'Blueprint'])
        rows = export_lean(manifest)
        audit = json.loads(args.audit_report.read_text()) if args.audit_report else None
        nodes = classify(manifest, rows, audit)
        if audit and audit.get('source_digest') != before['proof_source_digest']:
            raise ValueError('Full audit evidence is stale for the current Lean source digest')
        if snapshot() != before:
            raise RuntimeError('Sources changed during frontier validation')
        if audit:
            atomic_json(WORK / 'audit-evidence.json', {'source_digest': audit['source_digest'],
                        'checked_at': utc(), 'report': str(args.audit_report)})
        if args.check:
            print(json.dumps({'checked': len(nodes), 'revision': before['revision'],
                              'proof_source_digest': before['proof_source_digest']}), flush=True)
            return
        run(['lake', 'build', 'Model:blueprint', 'Spec:blueprint', 'Proofs:blueprint', 'Blueprint:blueprint'])
        if WEB.exists():
            shutil.rmtree(WEB)
        WEB.mkdir(parents=True)
        executable = shutil.which('leanblueprint')
        if not executable:
            raise RuntimeError('leanblueprint is unavailable')
        plastex = Path(executable).resolve().parent / 'plastex'
        run([plastex, '-c', 'plastex.cfg', 'web.tex'], PROJECT / 'blueprint/src')
        if snapshot() != before:
            raise RuntimeError('Sources changed during blueprint build; last served version retained')
        data = {**before, 'built_at': utc(), 'audit_status': audit_status, 'nodes': nodes}
        render_frontier(data)
        if snapshot() != before:
            raise RuntimeError('Sources changed while rendering; last served version retained')
        if args.publish:
            publish(data, args.destination, args.url)
        atomic_json(WORK / 'last-success.json', data)
        print(json.dumps({'built_at': data['built_at'], 'revision':data['revision'], 'url':args.url if args.publish else str(WEB)}), flush=True)


def install_watch():
    """Install the persistent macOS watcher without replacing another checkout's service."""
    label = 'com.safe-near.wnear-blueprint-watch'
    path = Path.home() / 'Library/LaunchAgents' / (label + '.plist')
    log = Path.home() / 'Library/Logs/safe-near-wnear-blueprint-watch.log'
    config = {'Label': label, 'ProgramArguments': [sys.executable, '-u', str(Path(__file__).resolve()), '--watch', '--publish', '--reuse'],
              'WorkingDirectory': str(ROOT), 'RunAtLoad': True, 'KeepAlive': True,
              'EnvironmentVariables': {'PATH': os.environ.get('PATH', '/usr/bin:/bin:/usr/sbin:/sbin')},
              'StandardOutPath': str(log), 'StandardErrorPath': str(log)}
    if path.exists():
        old = plistlib.loads(path.read_bytes())
        if old.get('WorkingDirectory') != str(ROOT):
            raise RuntimeError(f'{path} belongs to a different checkout; left unchanged')
        subprocess.run(['launchctl', 'bootout', f'gui/{os.getuid()}/{label}'], capture_output=True)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(plistlib.dumps(config))
    # launchd may briefly retain the old service after bootout succeeds.
    for attempt in range(10):
        result = subprocess.run(['launchctl', 'bootstrap', f'gui/{os.getuid()}', str(path)], capture_output=True, text=True)
        if result.returncode == 0:
            break
        if attempt == 9:
            raise RuntimeError(f'Unable to start {label}: {result.stderr.strip()}')
        time.sleep(0.5)
    print(f'Installed {label}; log: {log}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--install-watch', action='store_true', help='install a persistent macOS launchd watcher')
    parser.add_argument('--publish', action='store_true')
    parser.add_argument('--watch', action='store_true')
    parser.add_argument('--check', action='store_true', help='check actual frontier and exact audit allowlist without rendering')
    parser.add_argument('--reuse', action='store_true', help='publish a matching already-rendered build')
    parser.add_argument('--audit-report', type=Path)
    parser.add_argument('--destination', type=Path, default=DEFAULT_DEST)
    parser.add_argument('--url', default=DEFAULT_URL)
    args = parser.parse_args()
    if args.install_watch:
        install_watch()
        return 0
    if args.check and (args.publish or args.watch):
        parser.error('--check cannot be combined with --publish or --watch')
    previous = None
    failed_marker = None
    failures = 0
    retry_at = 0.0
    while True:
        current = snapshot()
        evidence = WORK / 'audit-evidence.json'
        marker = (current, evidence.stat().st_mtime_ns if evidence.exists() else 0)
        if marker != previous and (marker != failed_marker or time.monotonic() >= retry_at):
            try:
                build(args)
                previous = marker
                failed_marker = None
                failures = 0
            except Exception as error:
                print(f'{utc()} BLUEPRINT FAILURE: {error}', file=sys.stderr, flush=True)
                if args.publish:
                    atomic_json(args.destination / 'w-near-status.json', {'failure':str(error), 'failed_at':utc(), **current})
                if not args.watch:
                    return 1
                failures = failures + 1 if marker == failed_marker else 1
                failed_marker = marker
                retry_at = time.monotonic() + min(300, 10 * 2 ** min(failures - 1, 5))
        if not args.watch:
            return 0
        time.sleep(10)


if __name__ == '__main__':
    sys.exit(main())
