"""Deterministic local-redundancy identities for the paper's 20-row gadget.
Polynomial identities are checked coefficient-by-coefficient over Z, not by
random evaluation. Rank and numeric inequalities are checked over BN254 Fr.
"""
import json,time
from pathlib import Path
from analyze import jacobian,echelon,values
ROOT=Path(__file__).resolve().parent
P=21888242871839275222246405745257275088548364400416034343698204186575808495617

def add(*ps):
    out={}
    for poly in ps:
        for m,c in poly.items():out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}
def scale(p,c):return {m:a*c for m,a in p.items() if a*c}
def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}
def prod(ps):
    out={():1}
    for p in ps:out=mul(out,p)
    return out
def v(j):return {(j,):1}
def ev(poly,a):
    out=0
    for mon,c in poly.items():
        for j in mon:c*=a[j]
        out+=c
    return out%P

def main():
    started=time.perf_counter();x,s=0,1;us=list(range(2,7));ys=list(range(7,12));bs=list(range(12,20))
    zero=(0,{});one=(1,{});a=[0]*20;a[x]=3;rows=[];prev=x
    for u in us:
        rows.append(((0,{prev:1}),(0,{prev:1}),(0,{u:1})));a[u]=a[prev]**2%P;prev=u
    rows += [((0,{s:1}),(0,{y:1,u:-1}),zero) for y,u in zip(ys,us)]
    rows += [((0,{b:1}),(-1,{b:1}),zero) for b in bs]
    rows.append(((0,{**{b:2**i for i,b in enumerate(bs)},s:-1}),one,zero))
    rows.append(((0,{s:1}),(-1,{s:1}),zero))
    assert not any(values(rows,a,P))
    retained=list(range(5))+list(range(10,18))+[19]
    M=[{x:1}]+[jacobian(rows,a,P)[i] for i in retained]
    piv,free,expr,stats=echelon(M,20,P);assert len(piv)==15 and len(free)==5
    selector=mul(v(s),add(v(s),{():-1}));checks=[]
    for y,u in zip(ys,us):
        guard=mul(v(s),add(v(y),scale(v(u),-1)))
        left=mul(add(v(s),{():-1}),guard)
        right=mul(add(v(y),scale(v(u),-1)),selector)
        assert left==right
        checks.append({'type':'guard','target':y,'integer_coefficient_identity':True,'multiplier_value':str(P-1)})
    bitminus=[add(v(b),{():-1}) for b in bs]
    w=mul(add(v(s),{():-1}),prod(bitminus))
    g=add(*[scale(v(b),2**i) for i,b in enumerate(bs)],scale(v(s),-1))
    left=mul(w,g);right={}
    for i,b in enumerate(bs):
        q=scale(mul(add(v(s),{():-1}),prod(bitminus[:i]+bitminus[i+1:])),2**i)
        right=add(right,mul(q,mul(v(b),bitminus[i])))
    right=add(right,scale(mul(prod(bitminus),selector),-1));assert left==right
    assert ev(w,a)!=0
    checks.append({'type':'weighted_sum','integer_coefficient_identity':True,'multiplier_value':str(ev(w,a)),
                   'identity_monomials':len(left),'total_degree':max(map(len,left))})
    delta=2**14;d=5
    # Cube both sides to avoid floating-point exponents.
    degree_ok=P**3>=32**3*delta**13;dimension_ok=P>2*(d+1)*delta**2
    assert degree_ok and dimension_ok
    out={'prime':str(P),'constraints':20,'wires':20,'retained_constraints':retained,'fixing_coordinates':[0],
         'retained_augmented_rank':15,'retained_augmented_rows':15,'dimension':d,'quadratic_rows':14,
         'degree_upper_bound':delta,'deterministic_identities':checks,'degree_inequality':degree_ok,
         'dimension_inequality':dimension_ok,'target_value_lower_bound_rational':f'{P}/{2*delta}',
         'seconds':time.perf_counter()-started,'scope':'Synthetic 20-constraint example; no real-gadget smoothness certificate claimed'}
    (ROOT/'results'/'smoothness-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
    print('PASS: six exact integer-polynomial identities, nonzero local multipliers, rank 15/15, both Lang-Weil inequalities')
if __name__=='__main__':main()
