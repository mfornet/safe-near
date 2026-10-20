"""Independent causal assertions on each backend's raw, uncoarsened trace."""
from scenarios import ONE


def storage(block,account,key):
 return next(x['value']for x in block['storage']if x['account']==account and x['key']==list(key))


def check(raw,expect):
 trace=raw['trace'];blocks={b['label']:b for b in trace};checks=[]
 def require(condition,message):
  if not condition:raise AssertionError(message)
  checks.append(message)
 def marker(block):return storage(block,'observer.near',b'callback')
 def observer(block):return [o for o in block['outcomes']if o['executor']=='observer.near']
 require(not trace[-1]['pending']and trace[-1]['delayed']==0,'scenario settles all in-transit and delayed receipts')
 expected=expect['marker'];require(marker(trace[-1])==(None if expected is None else[expected]),'callback writes the expected success/failure marker, or rolls back on OOG')
 all_observer=[o for b in trace for o in observer(b)]
 require(len(all_observer)==1,'callback executes exactly once')
 require(all_observer[0]['status']['kind']==('failure'if expect.get('callbackFailure')else'value'),'callback execution status is correct')
 for b in trace:
  generated={r['id']:r for r in b['outgoing']}
  for o in b['outcomes']:
   for rid in o['receipts']:
    require(rid in generated and generated[rid]['body']['kind']=='action','execution outcome receipt IDs reference action envelopes')
 if expect['kind']=='withdraw':
  start=blocks['start withdrawal'];burn=blocks['withdrawal and waiting callback arrive']
  payout=blocks['release transfer'];delivered=blocks['deliver transfer result']
  callback=next(r for r in start['outgoing']if r['receiver']=='observer.near')
  withdrawal=next(r for r in start['outgoing']if r['receiver']=='wrap.near')
  transfer=next(r for r in burn['outgoing']if r['predecessor']=='wrap.near'and r['receiver']=='caller.near')
  outcome=next(o for o in burn['outcomes']if o['executor']=='wrap.near')
  require(outcome['status']=={'kind':'receipt','receiptId':transfer['id']},'withdrawal returns the payout receipt identity')
  require(transfer['body']['actions']==[{'kind':'transfer','deposit':str(10**22+1)}],'payout includes withdrawn amount and the attached yocto')
  require(transfer['body']['outputs']==withdrawal['body']['outputs'],'withdrawal forwards result listeners to payout')
  require([d['data_id']for d in transfer['body']['outputs']]==callback['body']['inputs'],'payout results satisfy the callback dependency')
  require(callback['body']['actions'][0]['gas']==(1 if expect.get('callbackFailure')else 20*10**12),'callback retains its original prepaid gas allocation')
  data=next(r for r in payout['outgoing']if r['body']['kind']=='data')
  require(data['body']['data']==(None if expect.get('transferFailure')else[]),'transfer emits failed data or successful empty bytes')
  require(data['body']['dataId']==callback['body']['inputs'][0],'result data uses the callback input identity')
  for label in ['withdrawal and waiting callback arrive','hold transfer, first empty block','hold transfer, second empty block','release transfer','hold result data']:
   require(marker(blocks[label])is None and not observer(blocks[label]),'callback cannot run before transfer result delivery: '+label)
  require(len(observer(delivered))==1,'last data arrival resumes the postponed callback in that same apply')
  held=blocks['hold transfer, first empty block'];held2=blocks['hold transfer, second empty block']
  require(held['pending']==held2['pending'],'empty delivery blocks preserve pending receipts exactly')
  key=b'a'+len('caller.near').to_bytes(4,'little')+b'caller.near'
  before=storage(blocks['quiet after deposit'],'wrap.near',key);after=storage(burn,'wrap.near',key)
  require(before is not None and after is not None and int.from_bytes(bytes(before),'little')-int.from_bytes(bytes(after),'little')==10**22,'burn commits before payout')
  require(storage(trace[-1],'wrap.near',key)==after,'later transfer/callback failure does not roll back the committed burn')
 else:
  start=blocks['start probe'];produced=blocks['deliver probe action']
  require(marker(produced)is None,'callback has not executed during production of its result data')
  data=[r for r in produced['outgoing']if r['body']['kind']=='data']
  require(len(data)==1,'finalized call emits exactly one result data envelope')
  require(data[0]['body']['data']==(list(b'ok')if expect['method']=='value'else None),'direct return or failure data matches the entire receipt outcome')
  if expect['method']=='storage':
   require(storage(trace[-1],'poor.near',b'large')is None,'post-VM storage-stake failure rolls back tentative storage')
   require(any(o['executor']=='poor.near'and o['status']['kind']=='failure'and 'lackbalanceforstate'in o['status']['error'].lower().replace('_','')for o in produced['outcomes']),'failure specifically comes from the post-VM storage stake check')
  if expect.get('dataFirst'):
   require(marker(blocks['deliver data before callback'])is None and not observer(blocks['deliver data before callback']),'early data is stored without fabricating a callback')
   require(len(observer(blocks['deliver callback and data']))==1,'callback arriving after data executes using stored input')
  if expect.get('lastNonCall'):
   root=next(o for o in start['outcomes']if o['executor']=='caller.near')
   require(root['status']=={'kind':'value','value':[]},'last non-call action overrides an earlier promise return')
  if expect.get('gasLimited'):
   require(produced['delayed']>0,'chunk gas limit retains unprocessed receipts in runtime delayed queue')
 return checks
