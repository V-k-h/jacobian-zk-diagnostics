"""Independent correctness checks and exhaustive controlled-query evaluation."""
import itertools,json,random,time
from pathlib import Path
from analyze import jacobian,echelon,directions,load
from certificate_checker import rank,values,line_certificate
ROOT=Path(__file__).resolve().parent
Z=(0,{})
def var(j):return (0,{j:1})
def const(c):return (c,{})

def controlled():
    # Each tuple: name, p, n, rows, witness, fixed, semantic target coordinates.
    return [
      ('affine_free',7,1,[],[0],{},[0]),
      ('hyperbola',7,2,[(var(0),var(1),const(1))],[1,1],{},[0,1]),
      ('guard_honest',7,2,[(var(0),(-1,{0:1}),Z),(var(0),var(1),Z)],[1,0],{},[1]),
      ('guard_degenerate',7,2,[(var(0),(-1,{0:1}),Z),(var(0),var(1),Z)],[0,0],{},[1]),
      ('guard_repaired',7,2,[(var(0),(-1,{0:1}),Z),(var(0),var(1),Z),(var(0),const(1),const(1))],[1,0],{},[1]),
      ('square_root',7,1,[(var(0),var(0),const(1))],[1],{},[0]),
      ('nonradical_square',7,1,[(var(0),var(0),Z)],[0],{},[0]),
      ('anisotropic_origin',7,3,[(var(0),var(0),var(2)),(var(1),var(1),(0,{2:-1}))],[0,0,0],{},[0,1]),
      ('ramified_parabola',7,2,[(var(0),var(0),var(1))],[0,0],{},[1]),
      ('coupled_roots',7,2,[((0,{0:1,1:1}),const(1),const(5)),(var(0),var(1),const(6))],[2,3],{},[0,1]),
      ('unique_chain',7,3,[(var(0),var(0),var(1)),(var(1),var(1),var(2))],[2,4,2],{0:2},[1,2]),
      ('iszero_benign_inverse',7,3,[(var(0),var(1),(1,{2:-1})),(var(0),var(2),Z),(var(2),(-1,{2:1}),Z)],[0,0,1],{0:0},[2])
    ]

def main():
    rng=random.Random(20261003);random_checks=0
    for p in (2,3,5,101):
        for _ in range(60):
            n=rng.randrange(1,8);m=rng.randrange(0,9)
            matrix=[{j:rng.randrange(p) for j in range(n)} for i in range(m)]
            matrix=[{j:c for j,c in r.items() if c} for r in matrix]
            piv,free,expr,_=echelon(matrix,n,p)
            dense=[[r.get(j,0) for j in range(n)] for r in matrix]
            assert len(piv)==rank(dense,p)
            for v in directions(expr,free,n):assert all(sum(c*v[j] for j,c in row.items())%p==0 for row in matrix)
            for j in range(n):assert bool(expr[j])==(rank(dense+[[int(i==j) for i in range(n)]],p)>len(piv))
            random_checks+=1
    exports=[]
    for path in sorted((ROOT/'exports').glob('*.json')):
        obj,p,rows,a,fixed,targets,_=load(path);assert not any(values(rows,a,p))
        J=jacobian(rows,a,p)
        # Independent exact directional central difference, valid since all exported p are odd.
        v=[rng.randrange(p) for _ in a];plus=[(x+y)%p for x,y in zip(a,v)];minus=[(x-y)%p for x,y in zip(a,v)]
        lhs=[(x-y)*pow(2,-1,p)%p for x,y in zip(values(rows,plus,p),values(rows,minus,p))]
        rhs=[sum(c*v[j] for j,c in row.items())%p for row in J];assert lhs==rhs
        dense_checked=False
        if len(a)<=100:
            M=[{j:1} for j in fixed]+J;piv,free,expr,_=echelon(M,len(a),p)
            assert len(piv)==rank([[r.get(j,0) for j in range(len(a))] for r in M],p);dense_checked=True
        exports.append({'name':obj['name'],'witness_verified':True,'directional_identity_checked':True,'dense_rank_crosscheck':dense_checked})
    controls=[]
    for name,p,n,rows,a,fixed,targets in controlled():
        assert not any(values(rows,a,p));M=[{j:1} for j in fixed]+jacobian(rows,a,p)
        piv,free,expr,_=echelon(M,n,p);moving=[j for j in targets if expr[j]]
        target_dim=rank([[expr[j].get(k,0) for k in free] for j in targets],p)
        solutions=[x for x in itertools.product(range(p),repeat=n) if all(x[j]==u for j,u in fixed.items()) and not any(values(rows,x,p))]
        counts={str(j):len({x[j] for x in solutions}) for j in targets}
        line_targets=set()
        for v in directions(expr,free,n):
            mt=[j for j in moving if v[j]]
            if mt and line_certificate(rows,a,v,fixed,mt[0],p) is not None:line_targets.update(mt)
        true=[j for j in moving if counts[str(j)]>1];false=[j for j in moving if counts[str(j)]==1]
        missed=[j for j in targets if j not in moving and counts[str(j)]>1]
        assert all(counts[str(j)]==p for j in line_targets)
        controls.append({'name':name,'prime':p,'constraints':len(rows),'solutions':len(solutions),'target_value_counts':counts,
                         'moving_targets':moving,'target_dimension':target_dim,'line_confirmed_targets':sorted(line_targets),
                         'confirmed_moving_targets':true,'spurious_for_nonuniqueness':false,'rigid_nonunique_targets':missed})
    # RQ5: original monic triangular equations w1^2=1, wi^2=w(i-1).
    # Prefix enumeration checks the exact roots independently of the degree product.
    multiplicity=[]
    p=257
    prefixes=[()]
    for q in (1,2,3):
        prefixes=[prefix+(v,) for prefix in prefixes for v in range(p) if v*v%p==(prefix[-1] if prefix else 1)]
        assert len(prefixes)==2**q
        multiplicity.append({'name':f'monic_square_chain_{q}','prime':p,'degrees':[2]*q,'leading_coefficients':[1]*q,
                             'certificate_type':'original monic triangular generators; no ideal-membership search',
                             'tuple_bound':2**q,'enumerated_tuples':len(prefixes),'last_target_values':len({x[-1] for x in prefixes})})
    # Exact integer-polynomial identity w*(w+u-5)-(wu-6)=w^2-5w+6.
    def add(*polys):
        out={}
        for poly in polys:
            for m,c in poly.items():out[m]=out.get(m,0)+c
        return {m:c for m,c in out.items() if c}
    assert add({(2,0):1,(1,1):1,(1,0):-5},{(1,1):-1,(0,0):6})=={(2,0):1,(1,0):-5,(0,0):6}
    multiplicity.append({'name':'coupled_roots','certificate_type':'exact coefficient identity plus original linear generator',
                         'degrees':[2,1],'leading_coefficients':[1,1],'tuple_bound':2,'enumerated_tuples':2})
    # Linear uniqueness and non-radical looseness are deliberate controls.
    multiplicity.extend([
      {'name':'linear_target','degrees':[1],'tuple_bound':1,'enumerated_tuples':1},
      {'name':'nonradical_square','degrees':[2],'tuple_bound':2,'enumerated_tuples':1,'note':'Upper bound need not be attained'},
      {'name':'hyperbola','certificate_type':'none supplied','verdict':'unknown; do not invent a triangular certificate'}])
    result={'random_matrix_crosschecks':random_checks,'exports':exports,'controlled_queries':controls,'multiplicity':multiplicity,
            'interpretation':'Designed controls and multiple witnesses of one real scalar-multiplication defect; not a representative vulnerability corpus.'}
    (ROOT/'results'/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS',random_checks,'random matrix checks;',len(exports),'exported witness/directional checks;',len(controls),'exhaustively solved controls;',len(multiplicity),'multiplicity records')
if __name__=='__main__':main()
