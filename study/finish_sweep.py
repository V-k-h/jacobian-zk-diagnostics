import json,sys,time
from pathlib import Path
from analyze import analyze,load,values
from line_search import search
ROOT=Path(__file__).resolve().parent
baseline=load(ROOT/'exports'/'scalar_12345_honest.json')
records=json.loads((ROOT/'results'/'witness-sweep-generation.json').read_text())
for r in records:
    if not r['witness_generated']:continue
    path=ROOT/'exports'/(r['name']+'.json');obj,p,rows,a,fixed,targets,digest=load(path)
    assert rows==baseline[2] and fixed==baseline[4] and not any(values(rows,a,p))
    r['diagnostic']=analyze(path)
    result=search(rows,a,fixed,targets,p);certs=result.pop('certificates',[])
    if certs:
        dest=ROOT/'results'/(r['name']+'_line_certificates.json')
        dest.write_text(json.dumps({'source':path.name,'source_sha256':digest,'certificates':certs},indent=2)+'\n');result['certificate_file']=dest.name
    r['complete_line_search']=result
    r['changed_from_honest_targets']=[j for j in targets if a[j]!=baseline[3][j]]
    r['same_relation_and_statement_verified']=True
(ROOT/'results'/'witness-sweep.json').write_text(json.dumps(records,indent=2)+'\n')
print('Verified sweep: all successful exports share the same relation and statement')
