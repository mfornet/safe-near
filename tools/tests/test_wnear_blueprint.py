"""Regression tests for truthful, fail-closed frontier classification."""
import copy
import json
from pathlib import Path
import sys
import unittest

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
import wnear_blueprint as blueprint


class FrontierPolicyTests(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads(blueprint.MANIFEST.read_text())
        self.nodes = {n['id']: n for n in self.manifest['nodes']}
        self.rows = []
        for n in self.manifest['nodes']:
            admission = n['kind'] == 'admission'
            self.rows.append({'declaration': n['declaration'], 'is_theorem': n['kind'] != 'verification_contract',
                              'direct_sorry': admission, 'shape_hash': n['reviewed_shape_hash'], 'blueprint_label': n['label'],
                              'not_ready': n['kind'] in ['verification_contract', 'admission'] or n['id'] in ['global', 'exported', 'dispatch', 'exported-clauses-assembly', 'global-composition', 'global-with-obligations', 'short-string-room', 'model-short-string-room', 'initial-memory-parser-room', 'initial-combined-parser-room', 'object-parser', 'array-parser', 'ignored-opening', 'storage', 'lookup-raw-absent', 'lookup-absent', 'balance-lookup-absent', 'balance-caller-absent', 'balance-export-call-absent', 'balance-export-call-and-copy', 'balance-export-format-zero', 'balance-export-call-copy-format', 'balance-export-through-expect', 'balance-export-through-return', 'balance-export-through-cleanup', 'balance-export-parsed-suffix', 'balance-export-state-read', 'balance-export-state-through-cleanup', 'balance-second-read-from-budget', 'balance-export-state-budget', 'balance-export-state-exact-gas', 'balance-room-after-state', 'balance-export-state-six-grows', 'borsh-vec-free-bound', 'borsh-bytes-reader-free-bound', 'borsh-bytes-free-bound', 'borsh-ft-free-bound', 'borsh-contract-reader-free-bound', 'borsh-contract-free-bound', 'state-read-free-bound', 'state-read-model-free-bound', 'balance-state-read-free-bound', 'balance-state-cleanup-free-bound', 'balance-next-budget-free-bound', 'balance-state-budget-free-bound', 'balance-state-exact-gas-free-bound', 'balance-state-six-grows-free-bound', 'parser-owned-resources', 'balance-parser-through-cleanup', 'parser-expose-heap', 'parser-fixed-resources', 'parser-fixed-through-cleanup', 'parser-public-through-cleanup', 'array-parser-copied-core', 'copied-parser-room', 'copied-parser-with-room', 'balance-copied-parser-through-cleanup', 'balance-input-deref-through-cleanup', 'balance-input-expect-through-cleanup', 'balance-input-through-cleanup', 'balance-input-setup-through-cleanup', 'balance-copied-absent-body', 'initial-input-copy-room', 'balance-copied-body-initial-room', 'balance-copied-absent-model-composition', 'balance-argument-length', 'balance-copied-body-gas-bound', 'receipt-input-register-bound', 'receipt-input-register-returns', 'no-input-mismatch-witness', 'input-read', 'method-ft_balance_of'], 'axioms': ['sorryAx'] if admission else ['propext'],
                              'type_dependencies': [], 'proof_dependencies': [], 'statement': 'test', 'type_hash': 1})
        self.by_id = {n['id']: row for n, row in zip(self.manifest['nodes'], self.rows)}
        for n in self.manifest['nodes']:
            self.by_id[n['id']]['proof_dependencies'] += [self.nodes[x]['declaration'] for x in n.get('required_proof_dependencies', [])]
        self.by_id['storage']['type_dependencies'] = [self.nodes['owned-room']['declaration']]
        self.by_id['lookup-raw-absent']['proof_dependencies'] = [self.nodes['storage-read-absent']['declaration']]
        self.by_id['lookup-absent']['proof_dependencies'] = [self.nodes['lookup-raw-absent']['declaration']]
        self.by_id['balance-lookup-absent']['proof_dependencies'] = [self.nodes['lookup-absent']['declaration']]
        self.by_id['balance-caller-absent']['proof_dependencies'] = [self.nodes['balance-lookup-absent']['declaration']]
        self.by_id['balance-export-call-absent']['proof_dependencies'] = [self.nodes['balance-caller-absent']['declaration']]
        self.by_id['balance-export-call-and-copy']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-call-absent', 'balance-export-copy-zero']]
        self.by_id['balance-export-call-copy-format']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-call-and-copy', 'balance-export-format-zero']]
        self.by_id['balance-export-through-expect']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-call-copy-format', 'balance-export-expect-ok']]
        self.by_id['balance-export-through-return']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-through-expect', 'balance-export-return-vec']]
        self.by_id['balance-export-through-cleanup']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-through-return', 'balance-export-cleanup']]
        self.by_id['balance-export-parsed-suffix']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-through-cleanup', 'balance-export-argument-copy']]
        self.by_id['balance-export-state-through-cleanup']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-state-read', 'balance-export-parsed-suffix']]
        self.by_id['balance-export-state-budget']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-state-through-cleanup', 'balance-second-read-from-budget']]
        self.by_id['balance-second-read-exact-gas']['proof_dependencies'] = [self.nodes['balance-next-read-cost-preserved']['declaration']]
        self.by_id['balance-export-state-exact-gas']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-state-budget', 'balance-second-read-exact-gas']]
        self.by_id['balance-export-state-six-grows']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-export-state-exact-gas', 'balance-room-after-state']]
        self.by_id['method-ft_balance_of']['axioms'].append('sorryAx')
        self.by_id['method-ft_balance_of']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['balance-no-issue', 'balance-accepted', 'balance-rejected']]
        self.by_id['global']['axioms'].append('sorryAx')
        self.by_id['global']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['exported', 'global-composition']]
        self.by_id['exported']['axioms'].append('sorryAx')
        self.by_id['exported']['proof_dependencies'] = [self.nodes[x]['declaration'] for x in ['dispatch', 'binary-size']] + [
            n['declaration'] for n in self.manifest['nodes'] if n['kind'] == 'admission' and not n.get('indirect_admission')] + [self.nodes['method-ft_balance_of']['declaration']]
        self.by_id['dispatch']['type_dependencies'] = [self.nodes['remaining']['declaration']]
        self.by_id['dispatch']['proof_dependencies'] = [n['declaration'] for n in self.manifest['nodes']
                                                        if n.get('method') and n['kind'] != 'admission' and not n.get('exported_direct')]
        for n in self.manifest['nodes']:
            self.by_id[n['id']]['type_dependencies'] += [self.nodes[x]['declaration'] for x in n.get('required_type_dependencies', [])]
        self.audit = {'violations': [{'declaration': n, 'axioms': ['sorryAx']}
                                     for n in self.manifest['expected_incomplete']]}

    def test_store_code_composition_preserves_external_frontier(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['balance-copied-body-store-code']['status'], 'Proven')
        self.assertIn({'id': 'balance-copied-body-store-code', 'status': 'Proven'},
                      result['balance-code-assembled']['integrated_into'])
        self.assertEqual(result['balance-code-start']['status'], 'Proven')
        self.assertNotIn('balance-accepted',
                         [n['id'] for n in result['balance-code-start']['integrated_into']])
        self.assertEqual(result['balance-accepted']['status'], 'Open')
        self.assertEqual(result['method-ft_balance_of']['status'], 'Conditional')
        self.assertEqual(result['global']['status'], 'Conditional')

    def test_store_code_cannot_claim_integration_without_checked_composition(self):
        self.by_id['balance-copied-body-store-code']['proof_dependencies'].remove(
            self.nodes['balance-code-assembled']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_initial_memory_discharges_this_parser_room_instance(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['balance-copied-body-initial-memory']['status'], 'Proven')
        self.assertNotIn('string-room', result['balance-copied-body-initial-memory']['type_edges'])
        self.assertNotIn('lookup-heap-room', result['balance-copied-body-initial-memory']['type_edges'])
        self.assertIn({'id': 'balance-copied-body-initial-memory', 'status': 'Proven'},
                      result['initial-memory-parser-room']['integrated_into'])
        self.assertEqual(result['string-room']['status'], 'Open')
        self.assertEqual(result['accept-parser']['status'], 'Open')
        self.assertEqual(result['method-ft_balance_of']['status'], 'Conditional')
        self.assertEqual(result['global']['status'], 'Conditional')

    def test_initial_memory_cannot_hide_a_remaining_room_hypothesis(self):
        self.by_id['balance-copied-body-initial-memory']['type_dependencies'].append(
            self.nodes['string-room']['declaration'])
        with self.assertRaisesRegex(ValueError, 'readiness does not match'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-copied-body-initial-memory']['proof_dependencies'].remove(
            self.nodes['initial-memory-parser-room']['declaration'])
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_admission_free_global_composition_keeps_contracts_open(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['exported-clauses']['status'], 'Open')
        for node in ['exported-clauses-assembly', 'global-composition', 'global-with-obligations']:
            self.assertEqual(result[node]['status'], 'Conditional')
            self.assertNotIn('sorryAx', result[node]['axioms'])
        self.assertIn({'id': 'global', 'status': 'Conditional'}, result['global-composition']['integrated_into'])

    def test_conditional_composition_and_unresolved_hypotheses_are_visible(self):
        result = {n['id']: n for n in blueprint.classify(self.manifest, self.rows, self.audit)}
        self.assertEqual(result['global']['status'], 'Conditional')
        self.assertEqual(result['context-wf-with-args']['status'], 'Proven')
        self.assertEqual(result['context-wf-bounded-args']['status'], 'Proven')
        self.assertEqual(result['input-register-trap']['status'], 'Proven')
        self.assertEqual(result['input-panic-obstruction']['status'], 'Proven')
        self.assertEqual(result['validated-actions-arguments']['status'], 'Proven')
        self.assertEqual(result['protocol-input-limit-order']['status'], 'Open')
        self.assertEqual(result['receipt-input-register-returns']['status'], 'Conditional')
        self.assertEqual(result['receipt-input-register-bound']['status'], 'Conditional')
        self.assertEqual(result['no-input-mismatch-witness']['status'], 'Conditional')
        self.assertEqual(result['dispatch']['status'], 'Conditional')
        self.assertEqual(result['object-parser']['status'], 'Conditional')
        self.assertEqual(result['ignored-opening']['status'], 'Conditional')
        self.assertEqual(result['array-parser']['status'], 'Conditional')
        self.assertEqual(result['storage']['status'], 'Conditional')
        self.assertEqual(result['input-register-room']['status'], 'Open')
        self.assertEqual(result['input-read']['status'], 'Conditional')
        self.assertEqual(result['balance-method-prologue']['status'], 'Proven')
        self.assertEqual(result['balance-input-expect']['status'], 'Proven')
        self.assertEqual(result['balance-input-deref-setup']['status'], 'Proven')
        self.assertEqual(result['balance-copied-absent-body']['status'], 'Conditional')
        self.assertEqual(result['initial-input-copy-room']['status'], 'Conditional')
        self.assertEqual(result['balance-copied-body-initial-room']['status'], 'Conditional')
        self.assertEqual(result['ft-balance-absent-model']['status'], 'Proven')
        self.assertEqual(result['balance-copied-absent-model-composition']['status'], 'Conditional')
        self.assertEqual(result['protocol-burn-limit']['status'], 'Open')
        self.assertEqual(result['balance-argument-charge']['status'], 'Proven')
        self.assertEqual(result['balance-argument-length']['status'], 'Conditional')
        self.assertEqual(result['balance-copied-body-gas-bound']['status'], 'Conditional')
        self.assertNotIn('input-register-room', self.nodes['balance-copied-body-initial-room']['required_type_dependencies'])
        self.assertNotIn('owned-room', self.nodes['balance-copied-body-initial-room']['required_type_dependencies'])
        self.assertEqual(result['balance-copied-parser-through-cleanup']['status'], 'Conditional')
        self.assertEqual(result['copied-parser-with-room']['status'], 'Conditional')
        self.assertEqual(result['parser-post-budget']['status'], 'Open')
        self.assertEqual(result['parser-fixed-result']['status'], 'Open')
        self.assertEqual(result['parser-public-through-cleanup']['status'], 'Conditional')
        self.assertEqual(result['parser-owned-result']['status'], 'Open')
        self.assertEqual(result['parser-owned-resources']['status'], 'Conditional')
        self.assertEqual(result['balance-parser-handoff']['status'], 'Proven')
        self.assertEqual(result['balance-parser-through-cleanup']['status'], 'Conditional')
        self.assertEqual(result['balance-next-read-free-bound']['status'], 'Open')
        self.assertEqual(result['balance-next-gas-free-bound']['status'], 'Open')
        self.assertEqual(result['balance-next-exact-gas-free-bound']['status'], 'Proven')
        self.assertEqual(result['balance-state-six-grows-free-bound']['status'], 'Conditional')
        self.assertEqual(result['state-entry-free-bound']['status'], 'Open')
        self.assertEqual(result['state-read-free-bound']['status'], 'Conditional')
        self.assertEqual(result['state-read-model-free-bound']['status'], 'Conditional')
        self.assertEqual(result['balance-state-entry']['status'], 'Open')
        self.assertEqual(result['balance-second-read']['status'], 'Open')
        self.assertEqual(result['balance-second-read-gas']['status'], 'Open')
        self.assertEqual(result['balance-second-read-from-budget']['status'], 'Conditional')
        self.assertEqual(result['balance-export-state-budget']['status'], 'Conditional')
        self.assertEqual(result['balance-second-read-exact-gas']['status'], 'Proven')
        self.assertEqual(result['balance-export-state-exact-gas']['status'], 'Conditional')
        self.assertEqual(result['balance-room-after-state']['status'], 'Conditional')
        self.assertEqual(result['balance-export-state-six-grows']['status'], 'Conditional')
        self.assertNotIn('owned-room', result['balance-export-state-six-grows']['type_edges'])
        self.assertNotIn('balance-second-read-gas', result['balance-export-state-exact-gas']['type_edges'])
        self.assertEqual(result['balance-export-state-read']['status'], 'Conditional')
        self.assertEqual(result['balance-export-state-through-cleanup']['status'], 'Conditional')
        self.assertIn({'id': 'balance-export-state-through-cleanup', 'status': 'Conditional'}, result['balance-export-parsed-suffix']['integrated_into'])
        self.assertEqual(result['ignore-hyp']['status'], 'Open')
        self.assertEqual(result['method-ft_total_supply']['status'], 'Proven')
        self.assertIn({'id': 'dispatch', 'status': 'Conditional'}, result['method-ft_total_supply']['integrated_into'])
        self.assertEqual(result['method-ft_balance_of']['status'], 'Conditional')
        self.assertEqual(sum(n['status'] == 'Open' for n in result.values() if n.get('method')), 8)

    def test_unlisted_admission_or_axiom_fails_closed(self):
        audit = copy.deepcopy(self.audit)
        audit['violations'].append({'declaration': 'WNear.untracked', 'axioms': ['sorryAx']})
        with self.assertRaisesRegex(ValueError, 'Untracked or stale audit frontier'):
            blueprint.classify(self.manifest, self.rows, audit)
        self.by_id['method-new']['axioms'].append('Lean.ofReduceBool')
        with self.assertRaisesRegex(ValueError, 'Nonstandard axioms'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_statement_weakening_and_stale_book_status_fail_closed(self):
        self.by_id['method-new']['shape_hash'] += 1
        with self.assertRaisesRegex(ValueError, 'Unreviewed statement or contract change'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['global']['not_ready'] = False
        with self.assertRaisesRegex(ValueError, 'readiness does not match'):
            blueprint.classify(self.manifest, self.rows, self.audit)

    def test_lost_composition_and_admission_changes_require_manifest_update(self):
        self.by_id['balance-export-state-six-grows']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-state-exact-gas']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-state-budget']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-state-through-cleanup']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-parsed-suffix']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-through-cleanup']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-through-return']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-through-expect']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-call-copy-format']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-call-and-copy']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-export-call-absent']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-caller-absent']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['balance-lookup-absent']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['lookup-absent']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['lookup-raw-absent']['proof_dependencies'].clear()
        with self.assertRaisesRegex(ValueError, 'Checked composition lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['dispatch']['proof_dependencies'].remove(self.nodes['method-new']['declaration'])
        with self.assertRaisesRegex(ValueError, 'lost dependencies'):
            blueprint.classify(self.manifest, self.rows, self.audit)
        self.setUp()
        self.by_id['method-near_withdraw']['direct_sorry'] = False
        with self.assertRaisesRegex(ValueError, 'Admission frontier changed'):
            blueprint.classify(self.manifest, self.rows, self.audit)




class PublishConfigurationTests(unittest.TestCase):
    def test_publishing_requires_an_explicit_endpoint(self):
        import contextlib
        import io
        from unittest.mock import patch
        with patch.object(blueprint, 'DEFAULT_URL', None), \
                patch.object(sys, 'argv', ['wnear_blueprint', '--publish']), \
                contextlib.redirect_stderr(io.StringIO()) as error:
            with self.assertRaises(SystemExit) as exit:
                blueprint.main()
        self.assertEqual(exit.exception.code, 2)
        self.assertIn('BLUEPRINT_BASE_URL', error.getvalue())

    def test_watcher_persists_the_configured_endpoint_and_destination(self):
        import plistlib
        import subprocess
        import tempfile
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as directory:
            home = Path(directory)
            destination = home / 'publish'
            url = 'https://example.com/w-near/'
            with patch.object(Path, 'home', return_value=home), \
                    patch.object(blueprint.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0)):
                blueprint.install_watch(destination, url)
            config = plistlib.loads((home / 'Library/LaunchAgents/com.safe-near.wnear-blueprint-watch.plist').read_bytes())
            arguments = config['ProgramArguments']
            self.assertEqual(arguments[arguments.index('--url') + 1], url)
            self.assertEqual(arguments[arguments.index('--destination') + 1], str(destination))


if __name__ == '__main__':
    unittest.main()
