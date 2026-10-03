import json
from pathlib import Path
D=Path(__file__).resolve().parent;d=json.loads((D/'compressed_templates.json').read_text());ps=d['optional_edges'];names=['u','v','c0','c1','c2','c3','a0','a1','b0','b1']
def es(edges):return '{'+', '.join(''.join(names[x] for x in e) for e in edges)+'}'
def bits(mask):return [e for i,e in enumerate(ps) if mask>>i&1]
head='''D ROUND 2 — INDEPENDENT FIRST COMPLETE DRAFT
Date: 2026-10-03. No E/C/sibling round-2 file or parent research route was read.

RESULT
The 1,144 supplied codegree-four certificates compress to ELEVEN literal signed-rim templates under the 192 allowed relabellings. Each template requires only 4 to 7 specified rim edges present and 2 to 4 specified rim edges absent; all other rim adjacencies are unrestricted. Every individual template has a universal elementary reducibility proof. Direct checking assigns one of the eleven to every supplied record and verifies the transferred witness.
This is a verified compression of the supplied catalogue, not yet a human proof that A1 and A2 force one of these patterns. No smallest-template or optimality claim is made.

FIXED TEMPLATE CLASS (specified before any minimum claim; no minimum claim is made)
The local graph has hubs u,v, common vertices C={c0,c1,c2,c3}, and private pairs A={a0,a1}, B={b0,b1}. Its thirteen fixed edges are uv; all uc and vc for c in C; ua0,ua1,vb0,vb1. The twenty-four optional rim edges are the six edges inside C; the eight C-A edges and a0a1; and the eight C-B edges and b0b1. Edges A-B are excluded from the local graph.
A signed-rim template is a FIXED, explicitly listed triple (S,D,R): S is a packing of triangles in the universal local graph with all optional rim edges present; D is a set of fixed hub edges; and R is a set of optional rim edges. The lists are not functions of the input graph. Only a permutation in (S4 x S2 x S2) semidirect S2 may be applied.
Define P to be the rim edges used by S. Define Dangerous(D) to be the set of optional rim edges xy for which there exists a hub h adjacent to x,y in the fixed local model, with neither hx nor hy in D. Define N = Dangerous(D) minus R. The template applies to a graph exactly when all P edges are present and all N edges are absent. Thus applicability is two bitset inclusions, not a search over arbitrary packings or covers.
For every listed template the following structural conditions hold:
(a) S is edge-disjoint in the universal local graph;
(b) P is a subset of R;
(c) every fixed triangle uvc contains an edge of D;
(d) |D|+|R| <= 2|S|.

UNIVERSAL SIGNED-RIM TRANSFER LEMMA
If (a)-(d) hold and P is present while N is absent, let X = D union (R intersect E(L)). Then (S,X) is a valid local reducibility certificate.
Proof: All hub edges of S are fixed and all its rim edges lie in P, hence are present; so S remains an edge-disjoint triangle packing in L. We have |X| <= |D|+|R| <= 2|S|. All S-edges avoiding the hubs lie in P subset R and are present, so they belong to X. For the covering condition, a triangle containing both hubs is uvc and meets D by (c). Every other triangle containing a hub is hxy for an optional rim edge xy. If hx or hy belongs to D, it is hit. Otherwise xy belongs to Dangerous(D). As xy is present and N is absent, xy cannot belong to N=Dangerous(D) minus R, so xy is in R intersect E(L), and the triangle is hit by X. These cases exhaust the triangles through either hub.
This proof does not use A1, A2, WKE testing, or any census. In an ambient graph, all triangles through u or v lie in L: their other two vertices are neighbors of that hub and therefore neither use an A-B edge nor leave the local vertex set. Thus adding arbitrary A-B edges or arbitrary edges leaving the rim cannot invalidate the certificate.

ELEVEN EXPLICIT TEMPLATES
Notation: concatenation denotes an edge or triangle on the named vertices. P lists mandatory-present rim edges; N lists mandatory-absent rim edges. D and R determine X as above. All unlisted optional edges are free. Each source key identifies a saved original certificate; applicability is NOT restricted to this source graph.
'''
parts=[head]
for i,t in enumerate(d['templates'],1):
 parts.append('\nT%d. Source key %s.\nP = %s\nN = %s\nS = %s\nD = %s\nR = %s\nBudget: %d + %d = %d = 2*%d.\n'%(i,t['key'],es(bits(t['required'])),es(bits(t['forbidden'])),es(t['packing']),es([e for e in t['cover'] if min(e)<2]),es([e for e in t['cover'] if min(e)>1]),sum(min(e)<2 for e in t['cover']),sum(min(e)>1 for e in t['cover']),len(t['cover']),len(t['packing'])))
parts.append('''
FOUR MECHANISMS IN THE ELEVEN LISTS
T1,T2,T3,T4,T6,T10: one triangle uvc and four single-hub triangles, with no outside triangle.
T7,T8: five single-hub triangles, no uvc and no outside triangle.
T9: six single-hub triangles, no uvc and no outside triangle.
T5,T11: one uvc, four single-hub triangles, and one triangle avoiding both hubs.
Thus every supplied configuration now has a witness with at most six triangles and at most one outside triangle. This is a catalogue consequence, not a universal theorem about every conceivable codegree-four local graph.

CATALOGUE EXTRACTION AND VERIFICATION
Only the supplied 1,144 records were inspected. No new admissible graphs were enumerated. The original census, original finder, and original verification main were not called.
For each original witness, retain its hub cover D. Let P be its used rim edges, and normalize its rim cover to R = P union (Dangerous(D) intersect E(L)). The original cover contains this R, so validity and budget persist. Five original witnesses lose one unnecessary cover edge; the other 1,139 keep their size. Setting N=Dangerous(D) minus R gives a universally valid signed template.
Modulo allowed relabelling, the resulting 1,144 witnesses give 499 distinct signed patterns (P,N). Retaining one valid witness per pattern is legitimate because every such witness proves exactly the same applicability test. The script tests each of these 499 pattern orbits against each of the supplied records by bitset inclusion. Greedy set cover followed by removal of redundant chosen members selects the eleven above. This is a heuristic selection within a fixed finite candidate class, and no minimum is asserted.
For every one of the 1,144 records the scripts save a template ID and an explicit allowed vertex permutation. They reconstruct the transferred S and X, and check every triangle edge, edge-disjointness, |X|<=2|S|, the rim-edge containment condition, and that every triangle containing u or v is hit. This literal validation succeeds for all 1,144 records.
The first selected template alone applies to 614 records. Under the saved assignment, 1,101 records receive a five-triangle packing and 43 a six-triangle packing; 1,109 records receive no outside triangle and 35 receive one. These assignment counts need not minimize outside-triangle use.

FILES AND REPRODUCTION
signed_patterns.py extracts and normalizes templates from the original JSON.
compress.py computes pattern coverage, chooses eleven, and checks all transferred certificates.
compressed_templates.json contains the eleven patterns, witnesses, all 192 allowed vertex permutations, and an assignment for each original record.
transformed_certificates.json contains all resulting literal certificates.
compression_summary.json reports counts and individual template coverage.
Run signed_patterns.py followed by compress.py. Both locate their output directory via Path(__file__).resolve().parent, so the working directory does not matter. signed_patterns.py reads the bundled normalized input ../input/B_codegree4_certificates.json; it does not access tuza-upstream or an absolute machine path. Auxiliary scripts analyze.py, show.py, and write_draft.py use the same portable convention.
Normalized bundled input SHA-256 (file bytes): 94c164cfe98180d73b839194735eb57ac97c5ab8203117110e6ad2d445070faf.
Canonical JSON SHA-256 (sort_keys=True, separators=(',',':'), ensure_ascii=False, UTF-8): 6c5cc50a669ce2934325284bdf1d654dfe5796db10fe6760ad33e9e1bc3aa953.
Dependency: compress.py requires NumPy, tested with NumPy 2.5.2; install with python -m pip install numpy if needed. The remaining reproduction scripts use the Python standard library. The bounded catalogue transformations finish in seconds here.

EXACT LOGICAL STATUS AND REMAINING GAP
Proved without enumeration: each of the eleven listed signed patterns universally implies reducibility, by the transfer lemma.
Verified on existing data: their relabelling orbits cover all 1,144 supplied records, with explicit validated witnesses.
Not proved structurally: every local graph satisfying connected non-WKE links and the degree budget contains one of the eleven signed patterns. Combining our coverage with the original paper's independently established catalogue completeness gives another computer-assisted proof, but does not replace that completeness argument by a human-readable one.
A focused next mathematical target is therefore the finite structural disjunction: A1+A2 implies T1 or ... or T11. The signed descriptions expose only 6 to 11 adjacency/nonadjacency conditions apiece, instead of a full 24-bit local graph, and may make a human classification feasible.
''')
(D/'proof.txt').write_text(''.join(parts),encoding='utf-8')
(D/'report.txt').write_text('''D round 2: eleven explicit signed-rim patterns cover all 1,144 supplied records under allowed relabellings. Each pattern specifies 4-7 present and 2-4 absent rim edges, with all others free, and has a universally valid packing/cover construction proved by a short transfer lemma. The fixed class is literal (S,D,R) templates; no arbitrary parameterization or minimum claim. A bounded NumPy incidence computation, greedy selection, and full literal verification produced compressed_templates.json and transformed_certificates.json. Every record now has <=6 packed triangles and <=1 outside triangle; 1,109 have none under the saved assignment. All scripts run in seconds. The unresolved gap is a human structural proof that A1+A2 force one of the eleven patterns, rather than relying on the original catalogue's completeness. No original enumeration/finder or sibling files read.\n''',encoding='utf-8')
print('First complete independent draft and report saved.')
