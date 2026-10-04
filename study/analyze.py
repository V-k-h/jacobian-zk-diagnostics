"""Exact sparse diagnostic for exported gnark R1CS, independent of earlier pilot.
No global uniqueness verdicts. Sparse row-echelon elimination uses smallest-wire
pivots (not the original paper's Markowitz heuristic). Timings describe this code.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import sys
import time
from certificate_checker import rank, line_certificate, affine, linear, values


def load(path):
    raw=Path(path).read_bytes(); obj=json.loads(raw); p=int(obj['prime'])
    rows=[]
    for row in obj['rows']:
        forms=[]
        for key in ('l','r','o'):
            const=0;coeff={}
            for t in row[key]:
                j,c=t['wire'],int(t['coefficient'])%p
                if j==-1:const=(const+c)%p
                else:coeff[j]=(coeff.get(j,0)+c)%p
            forms.append((const,{j:c for j,c in coeff.items() if c}))
        rows.append(tuple(forms))
    a=list(map(int,obj['values'])); fixed={j:a[j] for j in obj['fixed']}
    targets=obj.get('targets') or [j for j in range(len(a)) if j not in fixed]
    return obj,p,rows,a,fixed,targets,hashlib.sha256(raw).hexdigest()


def jacobian(rows,a,p):
    matrix=[]
    for l,r,o in rows:
        la,ra=affine(l,a,p),affine(r,a,p);row={}
        for form,factor in ((l,ra),(r,la),(o,-1)):
            for j,c in form[1].items():row[j]=(row.get(j,0)+factor*c)%p
        matrix.append({j:c for j,c in row.items() if c})
    return matrix


def echelon(matrix,n,p):
    pivots={}; peak_row=0; created=0; factor_nnz=0; updates=0
    for source in matrix:
        row=dict(source);peak_row=max(peak_row,len(row))
        while row:
            j=min(row)
            if j not in pivots:
                inv=pow(row[j],-1,p);row={k:c*inv%p for k,c in row.items()}
                pivots[j]=row;factor_nnz+=len(row);break
            factor=row[j];updates+=1
            for k,c in pivots[j].items():
                old=row.get(k,0);v=(old-factor*c)%p
                if v:
                    if not old:created+=1
                    row[k]=v
                else:row.pop(k,None)
            peak_row=max(peak_row,len(row))
    free=[j for j in range(n) if j not in pivots]
    expressions={j:{j:1} for j in free}
    for j in sorted(pivots,reverse=True):
        e={}
        for k,c in pivots[j].items():
            if k==j:continue
            for t,b in expressions[k].items():e[t]=(e.get(t,0)-c*b)%p
        expressions[j]={t:b for t,b in e.items() if b}
    return pivots,free,expressions,{'factor_nnz':factor_nnz,'peak_active_row_nnz':peak_row,
                                   'fill_insertions':created,'row_updates':updates}


def directions(expressions,free,n):
    return [[expressions[j].get(t,0) for j in range(n)] for t in free]


def analyze(path,certificates=True):
    start=time.perf_counter();obj,p,rows,a,fixed,targets,digest=load(path);load_s=time.perf_counter()-start
    t=time.perf_counter();assert not any(values(rows,a,p));verify_s=time.perf_counter()-t
    t=time.perf_counter();J=jacobian(rows,a,p);assemble_s=time.perf_counter()-t
    # Fixing rows first is part of this implementation's specified ordering.
    M=[{j:1} for j in fixed]+J
    t=time.perf_counter();pivots,free,expr,stats=echelon(M,len(a),p);rank_s=time.perf_counter()-t
    moving=[j for j in targets if expr[j]]
    target_rows=[[expr[j].get(k,0) for k in free] for j in moving]
    dimension=rank(target_rows,p) if target_rows else 0
    line_targets=set();checked=0;basis_pass=0;kernel_verified=True;line_s=0
    if certificates and len(free)<=32:
        t=time.perf_counter()
        for v in directions(expr,free,len(a)):
            assert all(sum(c*v[j] for j,c in row.items())%p==0 for row in M)
            relevant=[j for j in moving if v[j]]
            if not relevant:continue
            checked+=1
            b=line_certificate(rows,a,v,fixed,relevant[0],p)
            if b is not None:
                basis_pass+=1;line_targets.update(relevant)
        line_s=time.perf_counter()-t
    elif free:kernel_verified=False
    return {'name':obj['name'],'sha256':digest,'constraints':len(rows),'wires':len(a),
            'fixed':sorted(fixed),'targets_count':len(targets),'rank':len(pivots),'nullity':len(free),
            'all_free_coordinates':sum(bool(v) for v in expr.values()),'moving_targets':moving,
            'projected_target_dimension':dimension,'jacobian_nnz':sum(map(len,J)),
            'kernel_vectors_verified':kernel_verified,'line_vectors_checked':checked,
            'line_vectors_passed':basis_pass,'line_confirmed_targets':sorted(line_targets),
            'load_seconds':load_s,'verify_seconds':verify_s,'assembly_seconds':assemble_s,
            'rank_seconds':rank_s,'line_seconds':line_s,'analysis_total_seconds':time.perf_counter()-start,
            'compile_seconds':obj.get('compile_seconds'),'witness_solve_seconds':obj.get('solve_seconds'),
            'peak_rss_mib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/(1024**2 if sys.platform=='darwin' else 1024),
            **stats}


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('path');parser.add_argument('--no-certificates',action='store_true')
    args=parser.parse_args();print(json.dumps(analyze(args.path,not args.no_certificates)))
