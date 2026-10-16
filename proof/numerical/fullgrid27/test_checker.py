"""Fault injection tests. Re-pin ONLY the test inputs in a transient imported
checker instance so arithmetic failures are tested beyond the hash guard.
The production checker and its pins are never modified.
"""
import contextlib,importlib.util,io,json,shutil,sys,tempfile
from pathlib import Path
here=Path(__file__).resolve().parent;p=here.parents[1]
spec=importlib.util.spec_from_file_location('checker',here/'verify_grid.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
results=[]
with tempfile.TemporaryDirectory() as tmp:
 tmp=Path(tmp);base=p/'numerical/fullgrid27/grid_arithmetic.txt';trans=p/'numerical/external26/transcendental_values.txt'
 for name,kind,row,val,expected in [
  ('false_G_upper','grid',0,-10**12,'G bound'),
  ('false_knot_upper','grid',0,10**12,'knot bound'),
  ('false_log_pair','grid',1,-10**12,'pair bound'),
  ('wrong_log_argument','trans',22,1,'J identity'),
  ('false_distance_radius','trans',46,1,'cutoffs')]:
  path=tmp/('bad_'+kind+'.txt');shutil.copyfile(base if kind=='grid' else trans,path)
  with path.open('r+b') as f:
   if kind=='grid':f.seek(18*row);f.write(f'{val:+017d}\n'.encode())
   else:f.seek(4096+58*row+2);f.write(f'{val:016d}'.encode())
  m.GRID_SHA=m.sha(path) if kind=='grid' else m.sha(base)
  m.TRANS_SHA=m.sha(path) if kind=='trans' else m.sha(trans)
  sys.argv=['verify_grid.py','--project',str(p),'--cells','1','--out',str(tmp/'ignored.json'),'--'+kind,str(path)]
  try:
   with contextlib.redirect_stdout(io.StringIO()):m.main()
  except ValueError as e:
   assert expected in str(e),(name,str(e));results.append({'test':name,'rejected':True,'reason':str(e)})
  else:raise AssertionError('Accepted bad input: '+name)
  path.unlink()
r={'status':'PASS','tests':results,'scope':'Deliberately corrupted inputs; transient test-only hashes allow testing numerical rejection after the hash guard.'}
(here/'negative_controls.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
