import json,itertools,collections
from pathlib import Path
root=Path(__file__).resolve().parent
data=json.loads((root.parent/'shared'/'B_codegree4_certificates.json').read_text(encoding='utf-8-sig'))
def ed(t): return set(itertools.combinations(sorted(t),2))
stats=collections.Counter(); profiles=collections.Counter(); extra=collections.Counter(); rows=[]
for r in data['records']:
 s=r['packing']; x=set(map(tuple,r['cover'])); z=sum(0 in t and 1 in t for t in s); h=sum((0 in t) != (1 in t) for t in s); o=len(s)-z-h
 f={e for e in x if min(e)>1}; se=set().union(*(ed(t) for t in s)); sf={e for e in se if min(e)>1}
 spokes=len(x)-len(f)-(int((0,1) in x)); ex=len(f-sf)
 stats[(z,o,int((0,1) in x))]+=1; profiles[(z,h,o,spokes,ex)]+=1
 extra[(o,ex)]+=1
 rows.append({'key':[r['core_mask'],r['left_side_mask'],r['right_side_mask']],'z':z,'h':h,'o':o,'spokes':spokes,'extra_rim':ex,'s':s,'x':r['cover']})
print('central,outside,uvcovered',sorted(stats.items()))
print('outside,extra rim',sorted(extra.items()))
print('profiles',sorted(profiles.items()))
(root/'extracted_profiles.json').write_text(json.dumps(rows,indent=2))
