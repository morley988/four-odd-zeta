"""Two negative controls for the standalone checker; no large file copies."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json
from verify_values import verify
source=Path(__file__).with_name('transcendental_values.txt')
with source.open('rb') as f:header=f.read(4096);first=f.read(58)
results=[]
with TemporaryDirectory() as d:
 for name,row,expected in [('wrong_bound',first[:36]+f'{10**19:+021d}'.encode()+first[57:],'FAIL or inconclusive'),('truncated',first,'Wrong record count')]:
  p=Path(d)/name;p.write_bytes(header+row)
  try:verify(p,256)
  except ValueError as e:
   assert expected in str(e),str(e)
   results.append({'test':name,'correctly_rejected':True,'message':str(e)})
  else:raise AssertionError(f'{name} was incorrectly accepted')
Path(__file__).with_name('checker_negative_controls.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
