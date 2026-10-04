"""Fresh-process repeated measurements, raw data and witness-pair verification."""
import hashlib,json,platform,statistics,subprocess,sys,time
from pathlib import Path
from analyze import load,values
ROOT=Path(__file__).resolve().parent

def main():
    raw=[]
    for path in sorted((ROOT/'exports').glob('*.json')):
        for rep in range(5):
            start=time.perf_counter()
            proc=subprocess.run([sys.executable,str(ROOT/'analyze.py'),str(path)],capture_output=True,text=True,timeout=60,check=True)
            row=json.loads(proc.stdout);row['process_wall_seconds']=time.perf_counter()-start;row['repetition']=rep
            raw.append(row)
        print(path.stem, 'rank',row['rank'],'target_dim',row['projected_target_dimension'],
              'free',len(row['moving_targets']),'line',len(row['line_confirmed_targets']),flush=True)
    summaries=[]
    for name in sorted({r['name'] for r in raw}):
        samples=[r for r in raw if r['name']==name]
        stable=['rank','nullity','moving_targets','projected_target_dimension','line_confirmed_targets','sha256']
        assert all(all(r[k]==samples[0][k] for k in stable) for r in samples)
        row={k:v for k,v in samples[0].items() if not k.endswith('_seconds') and k!='repetition'}
        for key in [k for k in samples[0] if k.endswith('_seconds') or k=='peak_rss_mib']:
            vals=[r[key] for r in samples if r[key] is not None]
            row[key]={'median':statistics.median(vals),'min':min(vals),'max':max(vals)} if vals else None
        summaries.append(row)
    pairs=[]
    for scalar in (0,1,12345,54321):
        h=load(ROOT/'exports'/f'scalar_{scalar}_honest.json')
        z=load(ROOT/'exports'/f'scalar_{scalar}_zero_decomp.json')
        f=load(ROOT/'exports'/f'scalar_{scalar}_forged.json')
        assert h[2]==z[2]==f[2] and h[4]==z[4]==f[4]
        assert not any(values(h[2],h[3],h[1])) and not any(values(h[2],f[3],h[1]))
        changed=[j for j in h[5] if h[3][j]!=f[3][j]];assert changed
        pairs.append({'scalar':scalar,'honest_sha256':h[-1],'forged_sha256':f[-1],
                      'same_rows':True,'same_fixed_statement':True,'all_constraints_rechecked':True,
                      'changed_targets':changed,'honest_output':[str(h[3][j]) for j in h[5]],
                      'forged_output':[str(f[3][j]) for j in h[5]]})
    result={'environment':{'python':sys.version,'platform':platform.platform(),'machine':platform.machine()},
            'repetitions':5,'timing_scope':'Fresh interpreter per sample; warm filesystem caches, no cache flushing. Analysis total includes load, verify, assembly, rank and basis-line checks; process wall includes interpreter startup. Compile/solve timings are a single exporter run, repeated as metadata, not five independent measurements.',
            'raw':raw,'summary':summaries,'verified_scalar_pairs':pairs}
    (ROOT/'results'/'measurements.json').write_text(json.dumps(result,indent=2)+'\n')
    manifest={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'exports').glob('*.json'))}
    (ROOT/'results'/'export-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')

if __name__=='__main__':main()
