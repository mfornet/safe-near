"""Shared real-code inputs and controlled receipt delivery (not a network oracle)."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
ONE=10**24

def call(method,gas=200*10**12,deposit=0,args=b'{}'):
 return {'kind':'functionCall','method':method,'args':list(args),'gas':gas,'deposit':str(deposit)}
def incoming(receiver,actions,predecessor=None,**extra):
 defaults={'method':'','args':[],'gas':0,'deposit':'0','beneficiary':'','codePath':''}
 return {'receiver':receiver,'predecessor':predecessor or receiver,'actions':[{**defaults,**a}for a in actions],**extra}
def step(label,deliver='all',inject=None,**extra):
 return {'label':label,'deliver':deliver,'inject':inject or [],**extra}
def request():
 caller=ROOT/'tools/runtime-receipt-reference/fixtures/caller.wasm'
 contracts=[{'account':'wrap.near','codePath':str(ROOT/'contracts/w-near/contract.wasm'),'watPath':str(ROOT/'near-lean/vm/tests/fixtures/w_near.wat')}]
 for name in ['caller.near','observer.near','poor.near']:
  contracts.append({'account':name,'codePath':str(caller),'watPath':str(caller.with_suffix('.wat'))})
 keys=[{'account':'wrap.near','key':list(b'STATE')}]
 for name in ['caller.near','observer.near','poor.near']:
  key=b'a'+len(name).to_bytes(4,'little')+name.encode();keys.append({'account':'wrap.near','key':list(key)})
  keys += [{'account':name,'key':list(k)} for k in [b'callback',b'large']]
 return {'protocolVersion':86,'configDir':str(ROOT/'near-lean/vm/configs'),'contracts':contracts,
  'accounts':[{'id':name,'balance':str(2*ONE if name=='caller.near' else ONE//50 if name=='poor.near' else 100*ONE)} for name in ['caller.near','observer.near','poor.near','wrap.near','alice.near']],
  'inspectKeys':keys,
  'steps':[step('initialize',inject=[incoming('wrap.near',[call('new')])]),step('start deposit',inject=[incoming('caller.near',[call('deposit')])]),step('deposit reaches wrap'),step('settle deposit refunds'),step('quiet after deposit')]}
def withdrawal_scenario(fail_transfer=False,low_callback_gas=False):
 r=request();r['steps'] += [
  step('start withdrawal',inject=[incoming('caller.near',[call('withdraw_low_gas' if low_callback_gas else 'withdraw')])]),
  step('withdrawal and waiting callback arrive',['wrap.near','observer.near']),
  step('hold transfer, first empty block','none'),step('hold transfer, second empty block','none')]
 if fail_transfer:
  r['steps'].append(step('delete payout account before transfer','none',[incoming('caller.near',[{'kind':'deleteAccount','beneficiary':'alice.near'}])]))
 r['steps'] += [step('release transfer',['caller.near']),step('hold result data','none'),step('deliver transfer result',['observer.near']),step('settle refunds'),step('final quiet block')]
 return r
if __name__=='__main__':
 import json,sys
 print(json.dumps(withdrawal_scenario('--fail' in sys.argv,'--low-gas' in sys.argv)))


def probe_scenario(method='value',data_first=False,last_non_call=False,gas_limited=False):
 r=request()
 actions=[call('probe_'+method)]
 if last_non_call:actions.append({'kind':'transfer','deposit':'0'})
 r['steps'] += [step('start probe',inject=[incoming('caller.near',actions)]),
  step('deliver probe action',['poor.near' if method=='storage' else 'caller.near'] if data_first else 'all',gasLimit=1 if gas_limited else None),
  step('hold probe result','none')]
 if data_first:
  r['steps'] += [step('deliver data before callback',{'receivers':['observer.near'],'kind':'data'}),
                 step('hold callback after data','none')]
 r['steps'] += [step('deliver callback and data'),step('settle probe refunds'),step('probe quiet')]
 return r


def cases():
 yield 'withdraw-success',withdrawal_scenario(),{'kind':'withdraw','marker':1}
 yield 'withdraw-transfer-failure',withdrawal_scenario(True),{'kind':'withdraw','marker':2,'transferFailure':True}
 yield 'withdraw-callback-out-of-gas',withdrawal_scenario(False,True),{'kind':'withdraw','marker':None,'callbackFailure':True}
 r=withdrawal_scenario();r['steps'].insert(8,step('unrelated interleaving','none',[incoming('alice.near',[{'kind':'transfer','deposit':'1'}])]))
 yield 'withdraw-unrelated-interleaving',r,{'kind':'withdraw','marker':1}
 for method,marker in [('value',1),('panic',2),('storage',2)]:
  yield 'direct-'+method,probe_scenario(method),{'kind':'probe','method':method,'marker':marker}
 yield 'data-before-callback',probe_scenario(data_first=True),{'kind':'probe','method':'value','marker':1,'dataFirst':True}
 yield 'last-non-call-clears-return',probe_scenario(last_non_call=True),{'kind':'probe','method':'value','marker':1,'lastNonCall':True}
 yield 'chunk-gas-delay',probe_scenario(gas_limited=True),{'kind':'probe','method':'value','marker':1,'gasLimited':True}
