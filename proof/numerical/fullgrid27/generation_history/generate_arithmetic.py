from pathlib import Path
import numpy as np, hashlib, json
p=Path('work/Four_Value_Lean_Round20');g=np.load(p/'numerical/replay/round7_real_grid.npz')
G=g['G'];K=g['K']
f=p/'numerical/fullgrid27/grid_arithmetic.txt'
with f.open('w') as out:
 for k in range(50000):
  for x in [G[k],*K[:,k]]:
   s=f'{int(x):+017d}\n';assert len(s)==18;out.write(s)
print(f.stat().st_size,hashlib.file_digest(f.open('rb'),'sha256').hexdigest())
