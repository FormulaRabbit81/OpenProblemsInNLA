from pathlib import Path
import json,hashlib,argparse
from pypdf import PdfReader
from pypdf.generic import IndirectObject,StreamObject,DictionaryObject,ArrayObject,ByteStringObject,BooleanObject,NullObject
parser=argparse.ArgumentParser(); parser.add_argument('--repo',type=Path,default=Path('/private/tmp/nla-audit-261')); parser.add_argument('--out',type=Path,default=Path('/private/tmp/nla-review-261/pdf-resource-preservation.json')); args=parser.parse_args()
root=args.repo/'references/holden-ac-2026-09-14'
reports={'AC-01':'AC01_round3_research_pack/report/AC01_round3_report.pdf','AC-02':'AC02_updated_research_pack/round2/report/AC02_continuation.pdf','AC-03':'AC03_updated_pack/AC03_round3_verified/report.pdf','AC-04':'AC04_symmetric_extraction/report.pdf','AC-05':'AC05_power_rigidity/report/AC05_power_rigidity.pdf','AC-06':'AC06_round4/report.pdf'}
def normalized(obj,active=None):
 active=set() if active is None else active
 if isinstance(obj,IndirectObject): obj=obj.get_object()
 if id(obj) in active:return ['cycle']
 if isinstance(obj,(DictionaryObject,ArrayObject)):
  active=active|{id(obj)}
  if isinstance(obj,DictionaryObject):
   data={str(k):normalized(v,active) for k,v in sorted(obj.items()) if not(isinstance(obj,StreamObject) and k in ['/Length','/Filter','/DecodeParms'])}
   if isinstance(obj,StreamObject):data['_decoded_stream_sha256']=hashlib.sha256(obj.get_data()).hexdigest()
   return data
  return [normalized(v,active) for v in obj]
 if isinstance(obj,ByteStringObject):return ['bytes',bytes(obj).hex()]
 if isinstance(obj,BooleanObject):return bool(obj.value)
 if isinstance(obj,NullObject):return None
 return str(obj)
results={}
for ident,rel in reports.items():
 a=PdfReader(root/'submitted'/rel);b=PdfReader(root/(ident+'-submission.pdf'))
 hashes=[]
 for i,p in enumerate(a.pages):
  x=normalized(p.get('/Resources'));y=normalized(b.pages[i+1].get('/Resources'))
  if x!=y:raise ValueError((ident,i,'changed resource graph'))
  hashes.append(hashlib.sha256(json.dumps(x,sort_keys=True).encode()).hexdigest())
 results[ident]={'original_pages':len(a.pages),'all_page_resource_graphs_unchanged':True,'normalized_resource_sha256':hashes}
args.out.write_text(json.dumps(results,indent=2)+'\n')
print('PASS: resource graphs and decoded embedded font/image bytes match for all',sum(v['original_pages'] for v in results.values()),'original report pages')
