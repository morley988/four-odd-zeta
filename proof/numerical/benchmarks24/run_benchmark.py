from pathlib import Path
import subprocess,time,resource,json,sys
label,filename=sys.argv[1:]
start=time.perf_counter()
with Path('benchmarks24',label+'.log').open('w') as out:
 result=subprocess.run(['./run_lean.sh','env','lean',filename],stdout=out,stderr=subprocess.STDOUT)
r=resource.getrusage(resource.RUSAGE_CHILDREN)
data={'label':label,'file':filename,'exit_code':result.returncode,'wall_seconds':time.perf_counter()-start,'user_seconds':r.ru_utime,'system_seconds':r.ru_stime,'peak_rss_kib':r.ru_maxrss}
Path('benchmarks24',label+'.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(data),flush=True)
raise SystemExit(result.returncode)
