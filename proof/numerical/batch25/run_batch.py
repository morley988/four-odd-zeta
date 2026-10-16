from pathlib import Path
import subprocess,time,resource,json,sys,os
project=Path(os.environ.get("FOUR_VALUE_PROJECT","work/Four_Value_Lean_Round20")).resolve()
batchdir=Path(__file__).resolve().parent
runner=[str(Path("run_lean.sh").resolve())] if Path("run_lean.sh").exists() else ["lake"]
cell=int(sys.argv[1]);suffix=str(cell) if cell else ''
modules=['FourValueBatchEnclosures'+suffix,('FourValueBatchCell'+suffix if cell else 'FourValueBatchFirstCell')]
results=[]
for mod in modules:
 start=time.perf_counter();before=resource.getrusage(resource.RUSAGE_CHILDREN)
 with (batchdir/(mod+'.timed.log')).open('w') as log:
  r=subprocess.run(runner+['env','lean','-o','.lake/build/lib/lean/'+mod+'.olean',mod+'.lean'],cwd=project/"lean",stdout=log,stderr=subprocess.STDOUT)
 after=resource.getrusage(resource.RUSAGE_CHILDREN)
 row={'module':mod,'exit_code':r.returncode,'wall_seconds':time.perf_counter()-start,'cpu_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,'peak_rss_kib':after.ru_maxrss}
 results.append(row);print(json.dumps(row),flush=True)
 if r.returncode:break
out={'cell':cell,'modules':results,'success':len(results)==2 and all(r['exit_code']==0 for r in results),'total_wall_seconds':sum(r['wall_seconds']for r in results)}
(batchdir/f'timing{cell}.json').write_text(json.dumps(out,indent=2)+'\n')
raise SystemExit(0 if out['success'] else 1)
