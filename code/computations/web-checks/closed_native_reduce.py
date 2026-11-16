from collections import Counter
from itertools import combinations
from fractions import Fraction
from pathlib import Path
import json

def add(g,a,b):
 g.setdefault(a,Counter())[b]+=1;g.setdefault(b,Counter())[a]+=1

def delete(g,vs):
 out={a:Counter({b:m for b,m in ns.items() if b not in vs}) for a,ns in g.items() if a not in vs}
 return out

def comps(g):
 todo=set(g);out=[]
 while todo:
  s={todo.pop()};front=list(s)
  while front:
   a=front.pop()
   for b in g[a]:
    if b in todo:todo.remove(b);s.add(b);front.append(b)
  out.append(s)
 return out

def graph(subset):
 g={}
 for j in range(3):add(g,'C',f's{j}');add(g,'c',f'S{j}')
 port=[2,0,0,1,1,2]
 for pair in range(3):
  a,b=2*pair,2*pair+1
  if pair not in subset:
   for p in [a,b]:add(g,f's{port[p]}',f'S{port[p]}')
  else:
   add(g,f'H{pair}',f'h{pair}')
   for p in [a,b]:add(g,f's{port[p]}',f'H{pair}');add(g,f'S{port[p]}',f'h{pair}')
 return g

calls=[]
def ev(g,depth=0):
 if not g:return 1
 cc=comps(g)
 if len(cc)>1:
  out=1
  for c in cc:out*=ev({a:g[a] for a in c},depth+1)
  return out
 for a,ns in g.items():
  for b,m in ns.items():
   if m==3:
    assert len(g)==2
    calls.append(('theta',depth))
    return 6
   if m==2:
    aa=[n for n in g[a] if n!=b];bb=[n for n in g[b] if n!=a]
    assert len(aa)==len(bb)==1,(aa,bb)
    gg=delete(g,{a,b});add(gg,aa[0],bb[0])
    calls.append(('digon',depth))
    return 2*ev(gg,depth+1)
 sq=None
 for a in g:
  for b in g[a]:
   for c in g[b]:
    if c==a:continue
    for d in g[c]:
     if d in [a,b] or a not in g[d]:continue
     cycle=[a,b,c,d]
     rem=delete(g,set(cycle))
     # In a planar embedding, connected complement forces all other
     # vertices to one side, so the other side of this cycle is a face.
     if len(comps(rem))==1:sq=cycle;break
    if sq:break
   if sq:break
  if sq:break
 assert sq,repr(g)
 ext=[]
 for v in sq:
  ns=[n for n in g[v] if n not in sq]
  assert len(ns)==1,(sq,ns)
  ext.append(ns[0])
 calls.append(('square',depth))
 outs=[]
 for pairs in [[(0,1),(2,3)],[(0,3),(1,2)]]:
  gg=delete(g,set(sq))
  for i,j in pairs:add(gg,ext[i],ext[j])
  outs.append(ev(gg,depth+1))
 return sum(outs)

def print_values():
 global calls
 s=Fraction()
 for n in range(4):
  for sub in combinations(range(3),n):
   calls=[];val=ev(graph(sub));s+=(-Fraction(1,2))**n*val
   print(sub,'=',val,'reductions',','.join(a for a,d in calls))
 print('SUM',s,'bubble',s/6)

def one_square(g):
 for a in g:
  for b in g[a]:
   for c in g[b]:
    if c==a:continue
    for d in g[c]:
     if d in [a,b] or a not in g[d]:continue
     cycle=[a,b,c,d]
     rem=delete(g,set(cycle))
     if len(comps(rem))!=1:continue
     ext=[[n for n in g[v] if n not in cycle][0] for v in cycle]
     out=[]
     for pairs in [[(0,1),(2,3)],[(0,3),(1,2)]]:
      gg=delete(g,set(cycle))
      for i,j in pairs:add(gg,ext[i],ext[j])
      out.append(gg)
     return cycle,out

def one_digon(g):
 for a in g:
  for b,m in g[a].items():
   if m==2:
    aa=[n for n in g[a] if n!=b][0];bb=[n for n in g[b] if n!=a][0]
    gg=delete(g,{a,b});add(gg,aa,bb);return gg

def source(a):return a=='C' or a.startswith('S') or a.startswith('H')
def iso(g,h):
 if len(g)!=len(h):return False
 order=sorted(g,key=lambda a:(-max(g[a].values()),source(a)))
 mapping={};used=set()
 def step(i):
  if i==len(order):return True
  a=order[i]
  for b in h:
   if b in used or source(a)!=source(b) or sorted(g[a].values())!=sorted(h[b].values()):continue
   if any(g[a].get(x,0)!=h[b].get(y,0) for x,y in mapping.items()):continue
   mapping[a]=b;used.add(b)
   if step(i+1):return True
   used.remove(b);mapping.pop(a)
  return False
 return step(0)
C=one_digon(graph((0,)))
def print_isomorphism_checks():
 for sub,expected in [((0,1),[48,24]),((0,1,2),[48,48])]:
  sq,children=one_square(graph(sub))
  values=[ev(c) for c in children]
  assert values==expected
  if len(sub)==2:
   assert iso(children[1],C)
  else:
   assert all(iso(c,graph((0,))) for c in children)
  print('SQUARE',sub,sq,'branch values',values,'verified')

def serialize(g):
 return {'nodes':[{'id':a,'type':'source' if source(a) else 'sink'} for a in sorted(g)],'edges':[{'u':a,'v':b,'multiplicity':m} for a in sorted(g) for b,m in sorted(g[a].items()) if a<b]}

def prove(g):
 base={'graph':serialize(g)}
 if not g:return dict(base,rule='empty',value=1)
 cc=comps(g)
 if len(cc)>1:
  kids=[prove({a:g[a] for a in c}) for c in cc];val=1
  for k in kids:val*=k['value']
  return dict(base,rule='disjoint_product',children=kids,value=val)
 for a in g:
  for b,m in g[a].items():
   if m==3:
    assert len(g)==2
    return dict(base,rule='theta_is_digon_times_circle',factor=2,circle=3,value=6)
   if m==2:
    aa=[n for n in g[a] if n!=b][0];bb=[n for n in g[b] if n!=a][0]
    gg=delete(g,{a,b});add(gg,aa,bb);kid=prove(gg)
    return dict(base,rule='digon',vertices=[a,b],factor=2,reconnect=[aa,bb],child=kid,value=2*kid['value'])
 sq,gs=one_square(g)
 assert len(comps(delete(g,set(sq))))==1
 kids=[prove(gg) for gg in gs]
 return dict(base,rule='square',cyclic_face_vertices=sq,facial_certificate='complement_connected',children=kids,value=sum(k['value'] for k in kids))

def write_results(path='closed_native_results.json'):
 out={'conventions':{'circle':3,'digon':2,'square':'sum of the two oriented resolutions','packet_clasp':'P2=I-h/2'},'construction':{'central_vertices':['C','c'],'raw_tree_sink_pairs':[[2,3],[4,5],[6,1]],'packet_projection_pairs':[[1,2],[3,4],[5,6]],'sources':'C,Sj,Hj','sinks':'c,sj,hj'},'closures':[]}
 for n in range(4):
  for mask in combinations(range(3),n):
   p=prove(graph(mask));coef=(-Fraction(1,2))**n
   assert p['value']==[48,48,72,96][n]
   out['closures'].append({'h_projection_mask':[j+1 for j in mask],'coefficient':str(coef),'value':p['value'],'weighted_contribution':str(coef*p['value']),'proof':p})
 out['sum']=str(sum(Fraction(x['weighted_contribution']) for x in out['closures']))
 assert Fraction(out['sum'])==18
 out['packet_dimension']=6;out['bubble_scalar']=str(Fraction(out['sum'])/6)
 layout_path=Path('closed_native_results.json')
 if layout_path.exists():
  old=json.loads(layout_path.read_text())
  if 'diagram_layouts' in old:out['diagram_layouts']=old['diagram_layouts']
 Path(path).write_text(json.dumps(out,indent=2)+'\n')

if __name__ == "__main__":
 print_values()
 print_isomorphism_checks()
 write_results()
 print("Wrote closed_native_results.json using native reductions only.")
