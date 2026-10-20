#!/usr/bin/env python3
"""Compare receipt-result observations and retain full runtime trace diagnostics."""
import argparse,copy,hashlib,json,subprocess,sys
from pathlib import Path
from scenarios import ROOT,cases
from assertions import check

def normalize(value):
 trace=copy.deepcopy(value['trace']); receipts={};data={}
 def rid(x):
  if x not in receipts:raise ValueError(f'unknown receipt reference {x}')
  return receipts[x]
 def did(x):
  if x not in data:data[x]=f'd{len(data)}'
  return data[x]
 def receipt(r):
  r['id']=rid(r['id']);b=r['body']
  if b['kind']=='action':
   b['inputs']=[did(i)for i in b['inputs']]
   for d in b['outputs']:d['data_id']=did(d['data_id'])
  elif b['kind']=='data':b['dataId']=did(b['dataId'])
  else:raise ValueError('unknown receipt kind')
 def failure(error):
  lower=error.lower().replace('_','')
  if 'exceeded the prepaid gas' in lower:return 'gasexceeded'
  if 'smart contract panicked' in lower or 'guest panic' in lower:return 'guestpanic'
  for key in ['accountdoesnotexist','lackbalanceforstate','gaslimitexceeded','gasexceeded','guestpanic']:
   if key in lower:return key
  raise ValueError('unclassified runtime error: '+error)
 for i,b in enumerate(trace):
  for j,r in enumerate(b['incoming']):receipts.setdefault(r['id'],f'input:{i}:{j}')
  for j,r in enumerate(b['outgoing']):
   if r['id']in receipts:raise ValueError('reused outgoing receipt identity')
   receipts[r['id']]=f'output:{i}:{j}'
  for r in b['incoming']+b['outgoing']+b['pending']:receipt(r)
  for o in b['outcomes']:
   o['id']=rid(o['id']);o['receipts']=[rid(r)for r in o['receipts']]
   status=o['status']
   if status['kind']=='receipt':status['receiptId']=rid(status['receiptId'])
   if status['kind']=='failure':status['error']=failure(status['error'])
 return trace

def differences(a,b,path=''):
 if type(a)is not type(b):return [path+': type']
 if isinstance(a,dict):
  if a.keys()!=b.keys():return [path+': keys']
  return [p for k in a for p in differences(a[k],b[k],path+'/'+str(k))]
 if isinstance(a,list):
  if len(a)!=len(b):return [path+': length']
  return [p for i,(x,y)in enumerate(zip(a,b))for p in differences(x,y,path+'/'+str(i))]
 return []if a==b else[path+f': {a!r} != {b!r}']

def receipt_result_observation(trace):
 """Explicit result-delivery observation; full financial traces remain in report.

 Account balances and outcome gas/burn are outside this observation, as are the
 amounts of system refunds. Account existence/storage usage, all contract data,
 ordinary deposits, prepaid callback gas, routing, ordering, result identities,
 payloads, logs, queue lengths and execution statuses remain exact.
 """
 result=copy.deepcopy(trace)
 for b in result:
  for account in b['accounts'].values():
   if account is not None:account.pop('balance')
  for o in b['outcomes']:
   o.pop('gasBurnt');o.pop('tokensBurnt')
  for r in b['incoming']+b['outgoing']+b['pending']:
   if r['predecessor']=='system' and r['body']['kind']=='action':
    for a in r['body']['actions']:
     if a['kind']!='transfer':raise ValueError('noncanonical system refund')
     a.pop('deposit')
 return result


def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('reference',type=Path)
 p.add_argument('--scope',choices=['full','receipt-results'],default='full',help='full requires every gas/balance/refund observation too; receipt-results separately reports those differences')
 p.add_argument('--report',type=Path,default=ROOT/'audit/receipt-conformance.json')
 a=p.parse_args();results=[]
 manifest=json.loads((Path(__file__).parent/'fixtures/manifest.json').read_text())
 for key in ['wnear','caller']:
  item=manifest[key];path=ROOT/item['path']
  if hashlib.sha256(path.read_bytes()).hexdigest()!=item['sha256']:raise ValueError('fixture hash mismatch: '+key)
  if 'watSha256'in item and hashlib.sha256(path.with_suffix('.wat').read_bytes()).hexdigest()!=item['watSha256']:raise ValueError('WAT hash mismatch')
 for name,request,expect in cases():
  result={'name':name,'request':request,'expected':expect}
  try:
   raw=json.dumps(request)
   native=json.loads(subprocess.check_output([str(a.reference.resolve())],input=raw,text=True,cwd=ROOT))
   result['native']=native
   lean=json.loads(subprocess.check_output([str(ROOT/'near-lean/chain/.lake/build/bin/receipt-replay')],input=raw+'\n',text=True,cwd=ROOT))
   result['lean']=lean
   result['nativeAssertions']=check(native,expect)
   result['leanAssertions']=check(lean,expect)
   n,l=normalize(native),normalize(lean)
   result['fullTraceDifferences']=differences(n,l)
   result['receiptResultDifferences']=differences(receipt_result_observation(n),receipt_result_observation(l))
   result['passed']=not result['receiptResultDifferences'] and (a.scope!='full'or not result['fullTraceDifferences'])
  except Exception as error:
   result['passed']=False;result['error']=str(error)
  results.append(result)
  print(('PASS'if result['passed']else'FAIL')+': '+name,flush=True)
  for d in result.get('receiptResultDifferences',[])[:8]:print('  result: '+d,flush=True)
  if result.get('fullTraceDifferences'):print('  Full financial/gas trace differences: '+str(len(result['fullTraceDifferences'])),flush=True)
  if 'error'in result:print('  '+result['error'],flush=True)
 report={'referenceBinarySha256':hashlib.sha256(a.reference.resolve().read_bytes()).hexdigest(),
   'leanBinarySha256':hashlib.sha256((ROOT/'near-lean/chain/.lake/build/bin/receipt-replay').read_bytes()).hexdigest(),
   'sourceRevision':'44f7ae6cd7ef08bab604e20a473bf77e35d4c993',
   'scope':a.scope,'nativeSeam':'Pinned nearcore Runtime::apply / real trie / Wasmtime; externally supplied already-funded receipts and delivery schedule',
   'excludedFromReceiptResultObservation':['account balances','outcome gasBurnt and tokensBurnt','system refund transfer amounts'],
   'fixtures':manifest,'cases':results,'passed':sum(c['passed']for c in results),'failed':sum(not c['passed']for c in results)}
 a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(json.dumps(report,indent=2)+'\n')
 return int(any(not c['passed']for c in results))
if __name__=='__main__':sys.exit(main())
