import json,time,collections,itertools
from pathlib import Path
import numpy as np
D=Path(__file__).resolve().parent;data=json.loads((D/'signed_pattern_inputs.json').read_text());ts=data['templates'];rs=data['records'];maps=data['maps'];vs=data['vertex_maps'];pairs=list(map(tuple,data['optional_edges']))
def tr(mask,mp):
 out=0
 while mask:
  low=mask&-mask;out|=1<<mp[low.bit_length()-1];mask-=low
 return out
masks=np.array([r['mask'] for r in rs],dtype=np.uint32)
coverage=[]; witnesses=[]
for t in ts:
 required=np.array([tr(t['required'],m) for m in maps],dtype=np.uint32)
 forbidden=np.array([tr(t['forbidden'],m) for m in maps],dtype=np.uint32)
 hits=((masks[None,:]&required[:,None])==required[:,None])&((masks[None,:]&forbidden[:,None])==0)
 cover=hits.any(axis=0);first=hits.argmax(axis=0);first[~cover]=-1
 witnesses.append(first.tolist());coverage.append(sum(1<<i for i,x in enumerate(cover) if x))
incidence = {'format':'finite-signed-template-cover-v1','candidate_count':len(ts),'record_count':len(rs),'candidate_definition':'One candidate for each distinct Gamma-orbit of (P,N) obtained from the 1144 supplied certificates by D=X intersect fixed hub edges, R=P union (Dangerous(D) intersect E(L)), N=Dangerous(D) minus R. This is a fixed catalogue-derived dictionary, not all possible signed templates.','record_keys':[r['key'] for r in rs],'candidates':[{'id':j,'source_key':t['key'],'required_mask':t['required'],'forbidden_mask':t['forbidden'],'covered_records':[i for i in range(len(rs)) if coverage[j]>>i&1]} for j,t in enumerate(ts)]}
(D/'finite_cover_incidence.json').write_text(json.dumps(incidence,indent=2))
full=(1<<len(rs))-1;uncovered=full;chosen=[]
while uncovered:
 best=max(range(len(ts)),key=lambda j:(coverage[j]&uncovered).bit_count())
 assert coverage[best]&uncovered
 chosen.append(best);uncovered &=~coverage[best]
# Remove any redundant chosen member; this is greedy, not an exact minimum claim.
changed=True
while changed:
 changed=False
 for j in chosen[:]:
  covered=0
  for k in chosen:
   if k!=j:covered |=coverage[k]
  if covered==full:chosen.remove(j);changed=True;break
assign=[];base={(0,1)}|{(0,c) for c in range(2,8)}|{(1,c) for c in list(range(2,6))+[8,9]}
def te(t):return set(itertools.combinations(sorted(t),2))
packing_sizes=collections.Counter(); outside=collections.Counter(); transformed=[]
for i,r in enumerate(rs):
 j=next(j for j in chosen if coverage[j]>>i&1);p=witnesses[j][i];v=vs[p]
 s=[sorted(v[x] for x in t) for t in ts[j]['packing']]
 graph=base|{e for z,e in enumerate(pairs) if r['mask']>>z&1}
 x={tuple(sorted(v[z] for z in e)) for e in ts[j]['cover']}&graph
 used=set()
 for t in s:
  es=te(t);assert es<=graph and not (es&used);used|=es
 assert len(x)<=2*len(s)
 assert {e for e in used if min(e)>1}<=x
 for t in itertools.combinations(range(10),3):
  if 0 in t or 1 in t:
   es=te(t)
   if es<=graph:assert es&x
 assign.append({'key':r['key'],'template':chosen.index(j),'permutation_index':p})
 transformed.append({'key':r['key'],'packing':s,'cover':sorted(x)})
 packing_sizes[len(s)]+=1;outside[sum(not(0 in t or 1 in t) for t in s)]+=1
out={'format':'signed-rim-template-catalogue-v1','optional_edges':pairs,'vertex_permutations':vs,'templates':[ts[j] for j in chosen],'assignments':assign,'claims':{'records':len(rs),'templates':len(chosen),'selection_method':'greedy set cover plus redundant-member deletion; no minimum claimed'}}
(D/'compressed_templates.json').write_text(json.dumps(out,indent=2))
(D/'transformed_certificates.json').write_text(json.dumps(transformed,indent=2))
summary={'templates':len(chosen),'maximum_single_template_coverage':max(c.bit_count() for c in coverage),'selected':[{'index':k,'source_key':ts[j]['key'],'coverage':coverage[j].bit_count(),'required':ts[j]['required'].bit_count(),'forbidden':ts[j]['forbidden'].bit_count(),'packing_size':len(ts[j]['packing'])} for k,j in enumerate(chosen)],'packing_sizes':dict(packing_sizes),'outside_triangles':dict(outside)}
(D/'compression_summary.json').write_text(json.dumps(summary,indent=2))
print(json.dumps(summary,indent=2))
