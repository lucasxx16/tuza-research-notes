"""Check the exported witness and agreement of independently written records."""
from itertools import combinations
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]

def edge(a, b):
    return tuple(sorted((a, b)))

def main():
    d = json.loads((ROOT / 'equality/construction/certificates.json').read_text(encoding='utf-8'))
    b = json.loads((ROOT / 'equality/computation/graph_20.json').read_text(encoding='utf-8'))
    optimum = json.loads((ROOT / 'equality/computation/result_20.json').read_text(encoding='utf-8'))
    vertices = d['vertices']
    assert [v['id'] for v in vertices] == list(range(20))
    assert all(v['id'] == 5*(v['row']-1)+v['column']-1 for v in vertices)
    assert {(v['row'],v['column']) for v in vertices} == {(i,j) for i in range(1,5) for j in range(1,6)}
    edges = {edge(*e) for e in d['edges']}
    expected = {(a,b) for a,b in combinations(range(20),2) if a//5 == b//5 or a%5 == b%5}
    assert len(d['edges']) == len(edges) == 70
    assert edges == expected == {edge(*e) for e in b['edges_sorted']}
    degree = [sum(v in e for e in edges) for v in range(20)]
    assert degree == [7]*20
    reached = {0}
    while True:
        extended = reached | {v for e in edges if reached.intersection(e) for v in e}
        if extended == reached:
            break
        reached = extended
    assert len(reached) == 20
    triangles = {t for t in combinations(range(20),3) if all(edge(*e) in edges for e in combinations(t,2))}
    assert len(triangles) == 60
    assert set().union(*(set(combinations(t,2)) for t in triangles)) == edges
    packing = [tuple(sorted(t)) for t in d['packing']]
    assert len(packing) == len(set(packing)) == 13
    used = set()
    for t in packing:
        assert t in triangles
        te = set(combinations(t,2))
        assert not te.intersection(used)
        used.update(te)
    cover = {edge(*e) for e in d['cover']}
    assert len(cover) == len(d['cover']) == 26 and cover <= edges
    assert all(cover.intersection(combinations(t,2)) for t in triangles)
    assert optimum['nu_exact'] == 13 and optimum['tau_exact'] == 26
    result = {'status':'PASS', 'n':20, 'm':70, 'triangles':60,
              'connected':True, 'regular_degree':7, 'all_edges_in_triangles':True,
              'packing_size':13, 'cover_size':26, 'D_edges_equal_B_edges':True,
              'scope':'Exported certificate validity and record consistency. Optimality is proved in docs/equality.zh-CN.txt and separately computed by the exact verifier.'}
    (ROOT/'results/record_check.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result))

if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Do not disable assertions.')
    main()
