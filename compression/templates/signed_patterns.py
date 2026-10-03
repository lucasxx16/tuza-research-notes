import json,itertools,collections,time
from pathlib import Path
D=Path(__file__).resolve().parent
data=json.loads((D.parent/'input'/'B_codegree4_certificates.json').read_text(encoding='utf-8-sig'))
pairs=list(itertools.combinations(range(2,6),2))+[(c,a) for a in (6,7) for c in range(2,6)]+[(6,7)]+[(c,b) for b in (8,9) for c in range(2,6)]+[(8,9)]
idx={e:i for i,e in enumerate(pairs)}
base={(0,1)}|{(0,c) for c in range(2,8)}|{(1,c) for c in list(range(2,6))+[8,9]}
def bits(es): return sum(1<<idx[e] for e in es)
def key(r): return [r['core_mask'],r['left_side_mask'],r['right_side_mask']]
def rim(r): return r['core_mask']|(r['left_side_mask']<<6)|(r['right_side_mask']<<15)
def te(t): return set(itertools.combinations(sorted(t),2))
def maskmap(mask,perm):
 ans=0
 while mask:
  low=mask&-mask; i=low.bit_length()-1; ans|=1<<perm[i]; mask-=low
 return ans
maps=[]; vertexmaps=[]
for cp in itertools.permutations(range(2,6)):
 for aa in [(6,7),(7,6)]:
  for bb in [(8,9),(9,8)]:
   for swap in (0,1):
    vs=[0,1]+list(cp)+list(aa)+list(bb)
    if swap: vs=[1,0]+vs[2:6]+[x+2 for x in vs[6:8]]+[x-2 for x in vs[8:10]]
    maps.append([idx[tuple(sorted((vs[x],vs[y])))] for x,y in pairs]);vertexmaps.append(vs)
templates=[]
for r in data['records']:
 graph=base|{e for i,e in enumerate(pairs) if rim(r)>>i&1}
 x=set(map(tuple,r['cover']));s=r['packing']; packing_edges=set().union(*(te(t) for t in s))
 req={e for e in packing_edges if min(e)>1}
 hub=x&base
 danger=set()
 for e in pairs:
  for h in (0,1):
   spoke={(min(h,z),max(h,z)) for z in e}
   if spoke<=base and not (spoke&hub): danger.add(e)
 rr=req|(danger&graph)
 xx=hub|rr
 assert len(xx)<=2*len(s)
 assert all(t&xx for t in [te(t) for t in itertools.combinations(range(10),3) if te(t)<=graph and (0 in t or 1 in t)])
 forb=danger-rr
 p,n=bits(req),bits(forb)
 canon=min((maskmap(p,m),maskmap(n,m)) for m in maps)
 templates.append({'key':key(r),'required':p,'forbidden':n,'canonical':canon,'packing':s,'cover':sorted(xx),'old_cover_size':len(x),'new_cover_size':len(xx)})
unique={}
for t in templates:
 c=tuple(t['canonical'])
 if c not in unique:unique[c]=t
out={'optional_edges':pairs,'maps':maps,'vertex_maps':vertexmaps,'records':[{'key':key(r),'mask':rim(r)} for r in data['records']],'templates':list(unique.values())}
(D/'signed_pattern_inputs.json').write_text(json.dumps(out))
(D/'signed_patterns_all.json').write_text(json.dumps(templates,indent=2))
print('record count',len(templates),'unique signed pattern orbits',len(unique),'cover saving',dict(collections.Counter(t['old_cover_size']-t['new_cover_size'] for t in templates)))
print('presence,absence sizes',dict(collections.Counter((t['required'].bit_count(),t['forbidden'].bit_count()) for t in unique.values())))
