from pathlib import Path
import json,hashlib,numpy as np
r=Path(__file__).resolve().parent
if not __debug__:raise RuntimeError('Assertions must be enabled')
a=json.load(open(r/'original/round7_real_certificate.json'));b=json.load(open(r/'replay/round7_real_certificate.json'))
assert set(a)==set(b)
assert all(a[k]==b[k]for k in a if k!='seconds')
x=np.load(r/'original/round7_real_grid.npz');y=np.load(r/'replay/round7_real_grid.npz')
assert set(x.files)==set(y.files)=={'G','K'}
assert all(np.array_equal(x[k],y[k])for k in x.files)
h=hashlib.sha256((r/'replay/round7_real_grid.npz').read_bytes()).hexdigest()
assert h==a['grid_sha256']==b['grid_sha256']
result=dict(all_certificate_fields_except_elapsed_equal=True,all_grid_entries_equal=True,grid_sha256=h)
(r/'replay_comparison.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
