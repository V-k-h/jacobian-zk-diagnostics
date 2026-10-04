"""Bounded finite-field triangular root-search baseline and slice comparison.
This is an explicitly limited baseline, not an SMT/GB solver or a complete
uniqueness procedure. Both configurations use identical target seeds and solver.
"""
import argparse,hashlib,json,subprocess,sys,time
from pathlib import Path
from analyze import load,jacobian,echelon,values
ROOT=Path(__file__).resolve().parent


def reduce_form(form,known,p):
    c=form[0];out={}
    for j,a in form[1].items():
        if j in known:c+=a*known[j]
        else:out[(j,)]=a
    if c%p:out[()]=c%p
    return out


def reduce_row(row,known,p):
    l,r,o=[reduce_form(f,known,p) for f in row];poly={}
    for m,a in l.items():
        for n,b in r.items():
            key=tuple(sorted(m+n));poly[key]=(poly.get(key,0)+a*b)%p
    for m,a in o.items():poly[m]=(poly.get(m,0)-a)%p
    return {m:a for m,a in poly.items() if a}


def sqrt_mod(a,p):
    a%=p
    if not a:return 0
    if pow(a,(p-1)//2,p)!=1:return None
    if p%4==3:return pow(a,(p+1)//4,p)
    q=p-1;s=0
    while q%2==0:q//=2;s+=1
    z=2
    while pow(z,(p-1)//2,p)!=p-1:z+=1
    c=pow(z,q,p);x=pow(a,(q+1)//2,p);t=pow(a,q,p);m=s
    while t!=1:
        i=1;b=t*t%p
        while b!=1:b=b*b%p;i+=1
        factor=pow(c,1<<(m-i-1),p);x=x*factor%p;c=factor*factor%p;t=t*c%p;m=i
    return x


def roots(poly,j,p):
    c,b,a=poly.get((),0),poly.get((j,),0),poly.get((j,j),0)
    if not a:return [(-c*pow(b,-1,p))%p] if b else []
    if p==2:return [x for x in (0,1) if (a*x*x+b*x+c)%p==0]
    d=sqrt_mod((b*b-4*a*c)%p,p)
    if d is None:return []
    inv=pow(2*a,-1,p)
    return sorted({(-b+d)*inv%p,(-b-d)*inv%p})


def solve(rows,initial,old,p,seconds=10,max_nodes=1000):
    started=time.perf_counter();stats={'nodes':0,'linear_assignments':0,'root_branches':0,'row_reductions':0}
    def visit(known):
        stats['nodes']+=1
        while True:
            if time.perf_counter()-started>seconds or stats['nodes']>max_nodes:return 'unknown',None
            forced={};branch=None;remaining=False
            for row in rows:
                stats['row_reductions']+=1;poly=reduce_row(row,known,p)
                if not poly:continue
                remaining=True;vs={j for mon in poly for j in mon}
                if not vs:return 'unsat',None
                if len(vs)==1:
                    j=next(iter(vs));rs=roots(poly,j,p)
                    if not rs:return 'unsat',None
                    if len(rs)==1:
                        if j in forced and forced[j]!=rs[0]:return 'unsat',None
                        forced[j]=rs[0]
                    elif branch is None:branch=(j,rs)
            if forced:
                known={**known,**forced};stats['linear_assignments']+=len(forced);continue
            if not remaining:
                b=[known.get(j,x)%p for j,x in enumerate(old)]
                assert not any(values(rows,b,p));return 'sat',b
            if branch is None:return 'unknown',None
            j,rs=branch;unknown=False
            for x in rs:
                stats['root_branches']+=1;status,b=visit({**known,j:x})
                if status=='sat':return status,b
                if status=='unknown':unknown=True
            return ('unknown' if unknown else 'unsat'),None
    status,b=visit(dict(initial));return status,b,{**stats,'solve_seconds':time.perf_counter()-started}


def worker(path,mode):
    start=time.perf_counter();obj,p,rows,a,fixed,targets,digest=load(path)
    assert not any(values(rows,a,p));load_verify=time.perf_counter()-start
    initial=dict(fixed);diag=0;slicing=0;W=None
    if mode=='slice':
        t=time.perf_counter();M=[{j:1} for j in fixed]+jacobian(rows,a,p)
        _,_,expr,_=echelon(M,len(a),p);W={j for j,e in expr.items() if e};diag=time.perf_counter()-t
        if not W.intersection(targets):return {'name':obj['name'],'mode':mode,'status':'no_pointwise_candidate','total_seconds':time.perf_counter()-start}
        t=time.perf_counter();initial.update({j:x for j,x in enumerate(a) if j not in W})
        selected=[r for r in rows if any(j in W for f in r for j in f[1])]
        live=[r for r in selected if reduce_row(r,initial,p)]
        slicing=time.perf_counter()-t
    else:selected=rows;live=rows
    # Matched, explicitly narrower query: shift first output by one, preserve second.
    # This does not exhaust all possible second witnesses.
    initial[targets[0]]=(a[targets[0]]+1)%p
    for j in targets[1:]:initial[j]=a[j]
    status,b,stats=solve(live,initial,a,p,seconds=10)
    verified=False
    if b is not None:
        verified=not any(values(rows,b,p)) and all(b[j]==u for j,u in fixed.items()) and b[targets[0]]!=a[targets[0]]
        assert verified
    result={'name':obj['name'],'sha256':digest,'mode':mode,'status':status,'full_system_counterexample_verified':verified,
            'original_constraints':len(rows),'selected_constraints':len(selected),'live_constraints':len(live),
            'slice_coordinates':len(W) if W is not None else None,'load_verify_seconds':load_verify,
            'diagnostic_seconds':diag,'slicing_seconds':slicing,'total_seconds':time.perf_counter()-start,**stats}
    if b is not None:result['second_witness']=[str(x) for x in b]
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--worker');parser.add_argument('--mode');args=parser.parse_args()
    if args.worker:print(json.dumps(worker(args.worker,args.mode)));return
    results=[]
    for scalar in (0,1,12345,54321):
        path=ROOT/'exports'/f'scalar_{scalar}_zero_decomp.json'
        for mode in ('full','slice'):
            for repetition in range(3):
                t=time.perf_counter()
                try:
                    proc=subprocess.run([sys.executable,__file__,'--worker',str(path),'--mode',mode],capture_output=True,text=True,timeout=15,check=True)
                    row=json.loads(proc.stdout)
                except subprocess.TimeoutExpired:row={'name':path.stem,'mode':mode,'status':'process_timeout_15s'}
                row['process_wall_seconds']=time.perf_counter()-t;row['repetition']=repetition
                if 'second_witness' in row:
                    w=row.pop('second_witness');dest=ROOT/'results'/f'{path.stem}_{mode}_second_witness.json'
                    dest.write_text(json.dumps({'source':path.name,'values':w},indent=2)+'\n');row['witness_file']=dest.name
                results.append(row);print(path.stem,mode,repetition,row['status'],round(row.get('total_seconds',15),3),flush=True)
        (ROOT/'results'/'ablation.json').write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
