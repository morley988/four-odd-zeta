#!/usr/bin/env python3
"""Run from lean/ using `lake env python ../tools/serial_build.py MODULE ...`.
External dependency artifacts must come from the pinned Lake environment.
Project modules are rebuilt when their source or an imported artifact is newer.
"""
from pathlib import Path
import os,re,subprocess,sys
root=Path.cwd();out=root/'.lake/build/lib/lean';out.mkdir(parents=True,exist_ok=True)
stamps={};active=set()
def build(name):
 if name in stamps:return stamps[name]
 if name in active:raise RuntimeError('Cyclic import: '+name)
 active.add(name)
 relative=Path(name.replace('.','/')+'.lean');src=root/relative;dest=out;external=False
 if not src.exists():
  for package in (root/'.lake/packages').iterdir():
   candidate=package/relative
   if candidate.exists():src=candidate;dest=package/'.lake/build/lib/lean';external=True;break
  else:
   active.remove(name);stamps[name]=0;return 0
 target=dest/(name.replace('.','/')+'.olean')
 if external and target.exists():
  active.remove(name);stamps[name]=target.stat().st_mtime_ns;return stamps[name]
 newest=src.stat().st_mtime_ns
 for line in src.read_text().splitlines():
  match=re.match(r'(?:public |meta )*import (.+)',line)
  if match:
   for dep in match.group(1).split():newest=max(newest,build(dep))
 if not target.exists() or target.stat().st_mtime_ns<newest:
  target.parent.mkdir(parents=True,exist_ok=True)
  print('BUILD',name,flush=True)
  result=subprocess.run(['lean','--root',str(src.parents[len(name.split('.'))-1]),'-o',str(target),str(src)],env={**os.environ,'LEAN_NUM_THREADS':'1'})
  if result.returncode:
   target.unlink(missing_ok=True)
   raise SystemExit(result.returncode)
 active.remove(name);stamps[name]=target.stat().st_mtime_ns;return stamps[name]
for name in sys.argv[1:]:build(name)
print('SERIAL_BUILD_COMPLETE',flush=True)
