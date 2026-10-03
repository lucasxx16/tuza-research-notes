"""Export and literally verify B2's given optimal nine choices; no optimization."""
from pathlib import Path
import collections,hashlib,itertools,json
D=Path(__file__).resolve().parent
inputs=json.loads((D/'signed_pattern_inputs.json').read_text(encoding='utf-8-sig'))
selection=json.loads((D.parent/'B2'/'selected_cover.json').read_text(encoding='utf-8-sig'))
lower=json.loads((D.parent/'B2'/'lower_bound.json').read_text(encoding='utf-8-sig'))
incidence=json.loads((D/'finite_cover_incidence.json').read_text(encoding='utf-8-sig'))
raw=(D.parent/'shared'/'B_codegree4_certificates.json').read_bytes();original=json.loads(raw.decode('utf-8-sig'))
ids=selection['selected_candidate_ids'];assert ids==[7,78,195,214,316,329,387,428,491]
assert len(inputs['templates'])==499 and len(inputs['records'])==1144
pairs=list(map(tuple,inputs['optional_edges']));maps=inputs['maps'];vmaps=inputs['vertex_maps'];records=inputs['records']
base={(0,1)}|{(0,c) for c in range(2,8)}|{(1,c) for c in list(range(2,6))+[8,9]}
all_edges=base|set(pairs)
def triangles_edges(t):return set(itertools.combinations(sorted(t),2))
def transform(mask,mp):
 result=0
 while mask:
  low=mask&-mask;result|=1<<mp[low.bit_length()-1];mask-=low
 return result
orbit={j:[(transform(inputs['templates'][j]['required'],mp),transform(inputs['templates'][j]['forbidden'],mp)) for mp in maps] for j in ids}
# Verify each universal signed template independently of all catalogue records.
for j in ids:
 t=inputs['templates'][j];cover=set(map(tuple,t['cover']));hub=cover&base;rim=cover-base;used=set()
 for tri in t['packing']:
  es=triangles_edges(tri);assert es<=all_edges and not(es&used);used|=es
 required={e for e in used if min(e)>1};assert required<=rim
 assert len(cover)<=2*len(t['packing'])
 assert all(triangles_edges((0,1,c))&hub for c in range(2,6))
 dangerous=set()
 for e in pairs:
  for h in (0,1):
   spokes={tuple(sorted((h,z))) for z in e}
   if spokes<=base and not(spokes&hub):dangerous.add(e)
 assert t['required']==sum(1<<i for i,e in enumerate(pairs) if e in required)
 assert t['forbidden']==sum(1<<i for i,e in enumerate(pairs) if e in dangerous-rim)
assignments=[];transferred=[];sizes=collections.Counter();outside=collections.Counter();pure_core=0;assignment_counts=collections.Counter();coverages={}
for j in ids:
 coverages[j]=[i for i,r in enumerate(records) if any(r['mask']&p==p and r['mask']&n==0 for p,n in orbit[j])]
 assert coverages[j]==incidence['candidates'][j]['covered_records']
for i,r in enumerate(records):
 orig=original['records'][i]
 assert r['key']==[orig['core_mask'],orig['left_side_mask'],orig['right_side_mask']]
 assert r['mask']==orig['core_mask']|(orig['left_side_mask']<<6)|(orig['right_side_mask']<<15)
 match=next((j,k) for j in ids for k,(p,n) in enumerate(orbit[j]) if r['mask']&p==p and r['mask']&n==0)
 j,k=match;v=vmaps[k];t=inputs['templates'][j];graph=base|{e for z,e in enumerate(pairs) if r['mask']>>z&1}
 s=[sorted(v[z] for z in tri) for tri in t['packing']]
 x={tuple(sorted(v[z] for z in e)) for e in t['cover']}&graph
 used=set()
 for tri in s:
  es=triangles_edges(tri);assert es<=graph and not(es&used);used|=es
 assert len(x)<=2*len(s) and {e for e in used if min(e)>1}<=x
 for tri in itertools.combinations(range(10),3):
  if 0 in tri or 1 in tri:
   es=triangles_edges(tri)
   if es<=graph:assert es&x
 assignment={'record_index':i,'key':r['key'],'template':ids.index(j),'candidate_id':j,'permutation_index':k,'vertex_permutation':v}
 assignments.append(assignment);transferred.append(dict(assignment,packing=s,cover=sorted(x)))
 sizes[len(s)]+=1;outside[sum(not(0 in tri or 1 in tri) for tri in s)]+=1;pure_core+=sum(set(tri)<=set(range(2,6)) for tri in s);assignment_counts[j]+=1
witness=set(lower['packing_record_indices']);assert len(witness)==9
assert lower['packing_record_keys']==[records[i]['key'] for i in lower['packing_record_indices']]
assert all(len(witness&set(c['covered_records']))<=1 for c in incidence['candidates'])
scope='Minimum only within the fixed 499 Gamma-orbits of normalized signed patterns extracted from the supplied 1144 saved witnesses; not over all conceivable signed templates.'
templates=[dict(inputs['templates'][j],candidate_id=j) for j in ids]
output={'format':'optimal-signed-rim-template-catalogue-v1','scope':scope,'optional_edges':pairs,'vertex_permutations':vmaps,'candidate_ids':ids,'templates':templates,'assignments':assignments,'lower_bound_record_indices':lower['packing_record_indices'],'lower_bound_record_keys':lower['packing_record_keys']}
(D/'optimal_templates.json').write_text(json.dumps(output,indent=2),encoding='utf-8')
(D/'optimal_transformed_certificates.json').write_text(json.dumps(transferred,indent=2),encoding='utf-8')
summary={'status':'PASS','scope':scope,'candidate_ids':ids,'candidate_count':499,'record_count':1144,'optimal_template_count':9,'lower_bound':9,'upper_bound':9,'lower_bound_method':'Nine specified records; every one of the 499 saved candidate incidence rows covers at most one. Verified with exact integer sets.','lower_bound_record_indices':lower['packing_record_indices'],'lower_bound_record_keys':lower['packing_record_keys'],'universal_template_conditions_verified':True,'all_transferred_certificates_verified':True,'selected_incidence_rows_recomputed':True,'packing_sizes':dict(sizes),'outside_triangles':dict(outside),'pure_core_packed_triangles':pure_core,'per_candidate':[{'candidate_id':j,'source_key':inputs['templates'][j]['key'],'coverage':len(coverages[j]),'assigned':assignment_counts[j],'packing_size':len(inputs['templates'][j]['packing'])} for j in ids],'normalized_input_sha256':hashlib.sha256(raw).hexdigest(),'greedy_eleven_outputs':'preserved unchanged','gap':'No general human proof here that A1+A2 force one of the nine patterns; coverage is of the supplied catalogue.'}
(D/'optimum_summary.json').write_text(json.dumps(summary,indent=2),encoding='utf-8')
names=['u','v','c0','c1','c2','c3','a0','a1','b0','b1']
def display(es):return '{'+', '.join(''.join(names[z] for z in e) for e in es)+'}'
def mask_edges(mask):return [e for k,e in enumerate(pairs) if mask>>k&1]
descriptions={
7:'A core edge c0c2 has endpoints matched to the B pair, and a third common vertex c1 has an A neighbor a1. The absent edges c1c3,c3a1,c2b0 allow complementary spoke deletions. One central triangle and four single-hub triangles suffice.',
78:'The core is a star with two required leaves c2,c3 and one optional leaf c1, centered at c0. The required leaves have neighbors in opposite private pairs. Delete uv and all four private spokes, and cover the three possible core edges and two attachment edges.',
195:'The core consists of disjoint edges c0c3,c1c2 and the optional joining edge c0c1. Each core edge has its endpoints matched to a different private pair. Six single-hub triangles suffice, both when the core is 2K2 and when it is a four-vertex path.',
214:'An induced core path c0-c1-c2 has an A neighbor of endpoint c2 that misses c0,c1, and a B neighbor of the opposite endpoint c0. The fourth common vertex is unrestricted. This is the broad induced-path rule from the original eleven.',
316:'A triangle c0c3a0 avoids the hubs, a0a1 is present, and the disjoint core edge c1c2 has opposite B attachments. Three missing attachments permit a five-spoke cover. The packing has one central, four single-hub, and one outside triangle.',
329:'Two disjoint core edges have endpoints matched to the A and B pairs, respectively; three crossed attachments are absent. Six single-hub triangles suffice. The optional private edge a0a1 is included in the cover if present.',
387:'The core is an induced four-cycle, and one private pair is adjacent. Alternating cycle edges support four triangles at the two hubs, and the private edge supports the fifth. No attachment hypothesis is required.',
428:'The core contains the path c0-c2-c1-c3, with optional closing edge c0c3. Its middle edge supports outside triangle c1c2b1; specified A and B attachments support six additional single-hub triangles. Four missing edges permit a fourteen-edge cover.',
491:'The core contains path c1-c3-c2; its endpoints have opposite-side neighbors c2a0,c1b0. The unused private vertices a1,b1 miss all three of c1,c2,c3. The fourth common vertex c0 is unrestricted, and the optional edge c1c2 is covered if present. One central and four single-hub triangles suffice.'}
parts=['OPTIMAL NINE PATTERNS IN THE DECLARED FINITE DICTIONARY\n\n'+scope+'\n\nThe labels and universal signed-rim transfer lemma are as in proof.txt. Each list (S,D,R) is fixed. P denotes required-present rim edges and N required-absent rim edges. All unlisted optional adjacencies are free. Apply an allowed core/private-pair relabelling and optional hub/side exchange; then use X=D union (R intersect E(L)).\n']
for number,j in enumerate(ids,1):
 t=inputs['templates'][j];hub=[e for e in t['cover'] if min(e)<2];rim=[e for e in t['cover'] if min(e)>1]
 parts.append('\nO%d (candidate ID %d; source key %s).\n%s\nP = %s\nN = %s\nS = %s\nD = %s\nR = %s\nBudget: %d + %d = %d = 2*%d.\n'%(number,j,t['key'],descriptions[j],display(mask_edges(t['required'])),display(mask_edges(t['forbidden'])),display(t['packing']),display(hub),display(rim),len(hub),len(rim),len(t['cover']),len(t['packing'])))
parts.append('\nWHY NINE IS EXACT IN THIS DICTIONARY\nThe nine selected candidate IDs are '+str(ids)+'. Their relabelling orbits cover all 1,144 saved records. An assignment and literal valid witness are exported for every record. The lower-bound records have indices '+str(lower['packing_record_indices'])+' and keys '+str(lower['packing_record_keys'])+'. Every one of the 499 dictionary candidates covers at most one of these nine records, as checked exactly against the saved incidence matrix. Any cover therefore needs at least nine candidates; the selected nine attain this bound. This counting proof does not use a numerical solver bound.\n\nREPRODUCTION\nRun export_optimal.py after signed_patterns.py and compress.py. It reads the given selected IDs and lower-bound records from ../B2/selected_cover.json and ../B2/lower_bound.json, and the normalized source from ../shared/B_codegree4_certificates.json. It performs no optimization and needs only the Python standard library. It recomputes the selected incidence rows, verifies the universal conditions of each template, reconstructs and checks all 1,144 literal witnesses, and verifies the exact nine-record lower bound. The six pre-existing greedy mathematical output files are preserved.\n\nLOGICAL LIMIT\nThis is an exact optimum for the declared catalogue-derived finite dictionary and a universal proof for each chosen pattern. It is not an optimum over every possible signed template, and it does not supply the missing general human proof that A1+A2 force the nine-pattern disjunction.\n')
(D/'optimal_patterns.txt').write_text(''.join(parts),encoding='utf-8')
print(json.dumps(summary,indent=2))
