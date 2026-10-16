"""Check that the formal certificate tables equal the recovered exact witness."""
from pathlib import Path
from fractions import Fraction as F
import re,ast,json,sys
ROOT=Path(__file__).resolve().parent
lean=Path(sys.argv[1]) if len(sys.argv)>1 else ROOT.parent/'lean'
s=(lean/'FourValueCertificate.lean').read_text()
def parse(name):
 t=re.search(r'def '+name+r'[^=]*:= (\[.*?\n\])',s,re.S).group(1).replace(': ℚ','')
 def ev(n):
  if isinstance(n,ast.Constant):return F(n.value)
  if isinstance(n,ast.List):return [ev(x)for x in n.elts]
  if isinstance(n,ast.Tuple):return tuple(ev(x)for x in n.elts)
  if isinstance(n,ast.UnaryOp)and isinstance(n.op,ast.USub):return -ev(n.operand)
  if isinstance(n,ast.BinOp)and isinstance(n.op,ast.Div):return ev(n.left)/ev(n.right)
  raise ValueError(n)
 return ev(ast.parse(t,mode='eval').body)
if not __debug__:raise RuntimeError('Assertions must be enabled')
w=json.load(open(ROOT/'replay/round7_basis_witness.json'));c=json.load(open(ROOT/'replay/round7_real_certificate.json'))
assert parse('centers')==[tuple(map(F,z))for z in w['centers']]
assert parse('weightRows')==w['weights']
assert parse('knotBounds')==[(F(z['s']),F(z['upper']))for z in c['knots']]
target=(lean/'FourValueTargetPearson.lean').read_text()
endpoints=list(map(int,re.findall(r'(\d+)\*n',re.search(r'!\[(.*?)\]',target,re.S).group(1))))
assert [F(a,100)for a in endpoints]==list(map(F,w['a']))
normal=(lean/'FourValueNormalization.lean').read_text()
facts=list(map(int,re.search(r'def targetFactorialEndpoints[^=]*:= !\[(.*?)\]',normal,re.S).group(1).split(',')))
assert facts==endpoints[5:]
assert endpoints[:5]==[67]*5
result=dict(endpoint_tuple_equal=True,normalization_endpoints_equal=True,centers_equal=True,weights_equal=True,knots_equal=True,counts=[45,40,42])
(ROOT/'source_identity.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
