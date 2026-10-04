"""Complete projective search for affine-line certificates when kernel dimension <=2."""
import json,time
from pathlib import Path
from analyze import load,jacobian,echelon,directions,linear
from certificate_checker import line_certificate
ROOT=Path(__file__).resolve().parent

def search(rows,a,fixed,targets,p):
    M=[{j:1} for j in fixed]+jacobian(rows,a,p)
    _,free,expr,_=echelon(M,len(a),p);B=directions(expr,free,len(a));k=len(B)
    if k==0:return {'nullity':0,'complete':True,'target_moving_line_exists':False,'reason':'zero tangent space'}
    if k>2:return {'nullity':k,'complete':False,'reason':'dimension exceeds search scope'}
    candidates=[]
    if k==1:candidates=[B[0]]
    else:
        # Q_i(alpha,beta) factors as two linear forms. If any Q_i is
        # nonzero, every solution lies on one of its two projective roots.
        # Both factors are over F_p; no univariate factorization is needed.
        candidates=B
        for l,r,o in rows:
            l0,l1=linear(l,B[0],p),linear(l,B[1],p)
            r0,r1=linear(r,B[0],p),linear(r,B[1],p)
            if (l0 or l1) and (r0 or r1):
                candidates=[]
                for alpha,beta in ((-l1,l0),(-r1,r0)):
                    candidates.append([(alpha*x+beta*y)%p for x,y in zip(B[0],B[1])])
                break
    valid=[];certificates=[]
    for v in candidates:
        moving=[j for j in targets if v[j]]
        b=line_certificate(rows,a,v,fixed,moving[0],p) if moving else None
        if b is not None:
            valid.append(moving);certificates.append({'direction':{str(j):str(x) for j,x in enumerate(v) if x},'second_witness':[str(x) for x in b]})
    return {'nullity':k,'complete':True,'target_moving_line_exists':bool(valid),
            'projective_candidates_checked':len(candidates),'certified_target_supports':valid,'certificates':certificates}


def main():
    out=[]
    for path in sorted((ROOT/'exports').glob('*.json')):
        obj,p,rows,a,fixed,targets,digest=load(path)
        if len(a)>3000:continue
        started=time.perf_counter();result=search(rows,a,fixed,targets,p);elapsed=time.perf_counter()-started
        certs=result.pop('certificates',[])
        if certs:
            dest=ROOT/'results'/f"{obj['name']}_line_certificates.json"
            dest.write_text(json.dumps({'source':path.name,'source_sha256':digest,'certificates':certs},indent=2)+'\n')
            result['certificate_file']=dest.name
        out.append({'name':obj['name'],'sha256':digest,'search_including_rank_seconds':elapsed,**result})
    (ROOT/'results'/'complete-line-search.json').write_text(json.dumps(out,indent=2)+'\n')
    print('\n'.join(f"{r['name']}: complete={r['complete']} target line={r.get('target_moving_line_exists')}" for r in out))
if __name__=='__main__':main()
