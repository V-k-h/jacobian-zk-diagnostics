"""Exhaustive small-field oracle checks for the bounded solver and line search."""
import itertools,json,random
from pathlib import Path
from solve_ablation import solve,sqrt_mod
from line_search import search
from certificate_checker import values,line_certificate
ROOT=Path(__file__).resolve().parent
rng=random.Random(20261004);solver_cases=0;line_cases=0;statuses={}
for p in (2,3,5,7):
    for _ in range(30):
        n=2
        def form():return (rng.randrange(p),{j:rng.randrange(p) for j in range(n)})
        rows=[(form(),form(),form()) for _ in range(rng.randrange(4))]
        fixed={0:rng.randrange(p)} if rng.randrange(2) else {}
        actual=[v for v in itertools.product(range(p),repeat=n) if all(v[j]==x for j,x in fixed.items()) and not any(values(rows,v,p))]
        status,b,stats=solve(rows,fixed,[0]*n,p,seconds=1)
        statuses[status]=statuses.get(status,0)+1
        if status=='sat':assert tuple(b) in actual
        elif status=='unsat':assert not actual
        solver_cases+=1
        if actual:
            a=list(actual[0]);r=search(rows,a,fixed,[0,1],p)
            assert r['complete']
            exists=any(line_certificate(rows,a,list(v),fixed,j,p) is not None for v in itertools.product(range(p),repeat=n) for j in (0,1))
            assert exists==r['target_moving_line_exists'];line_cases+=1
P=21888242871839275222246405745257275088548364400416034343698204186575808495617
for p in (3,5,7,101,P):
 for i in range(20):
    a=rng.randrange(p);root=sqrt_mod(a*a%p,p);assert root is not None and root*root%p==a*a%p
result={'solver_oracle_cases':solver_cases,'solver_status_counts':statuses,'random_complete_line_search_oracle_cases':line_cases,'modular_square_root_checks':100,'passed':True}
(ROOT/'results'/'solver-validation.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',result)
