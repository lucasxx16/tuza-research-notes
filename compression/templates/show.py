import json
from pathlib import Path
D=Path(__file__).resolve().parent;d=json.loads((D/'compressed_templates.json').read_text());ps=d['optional_edges']
names=['u','v','c0','c1','c2','c3','a0','a1','b0','b1']
def es(edges):return '{'+', '.join(''.join(names[x] for x in e) for e in edges)+'}'
def bits(mask):return [e for i,e in enumerate(ps) if mask>>i&1]
for i,t in enumerate(d['templates'],1):
 print('T'+str(i),'source',t['key'])
 print('P =',es(bits(t['required'])))
 print('N =',es(bits(t['forbidden'])))
 print('S =',es(t['packing']))
 print('D =',es([e for e in t['cover'] if min(e)<2]))
 print('R =',es([e for e in t['cover'] if min(e)>1]))
