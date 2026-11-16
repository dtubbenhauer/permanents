from itertools import permutations, product
from fractions import Fraction

def sign(t):
    if len(set(t)) != 3:
        return 0
    return (-1)**sum(t[i] > t[j] for i in range(3) for j in range(i+1,3))
# Upper half in the new seam drawing. Its black vertices take legs 23,45,61.
def half(a):
    return sum(sign(t)*sign((t[0],a[1],a[2]))*sign((t[1],a[3],a[4]))*sign((t[2],a[5],a[0])) for t in permutations(range(3)))
raw={a:half(a) for a in product(range(3),repeat=6)}
def reorder(a,sw):
    return tuple(a[2*j+(b^sw[j])] for j in range(3) for b in range(2))
def projected(a):
    return Fraction(sum(raw[reorder(a,sw)] for sw in product([0,1],repeat=3)),8)
v=sum(projected(a)**2 for a in raw)
assert v==18
print('Closed six-port picture with clasps 12|34|56 =',v)
