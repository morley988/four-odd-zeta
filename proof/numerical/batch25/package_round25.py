from pathlib import Path
import json,hashlib,zipfile,datetime,shutil
root=Path('work/Four_Value_Lean_Round20');p=root/'lean';v=json.loads((p/'verification.json').read_text())
assert v['end_to_end_certificate_batch_verified'] and v['build_success'] and v['axiom_audit_complete']
assert not v['numerical_certificate_stage_complete_in_lean']
base=json.loads((p/'baseline_preservation.json').read_text());assert len(base)==221
for n,h in base.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
b=root/'numerical/batch25';b.mkdir(exist_ok=True)
for f in Path('batch25').iterdir():
 if f.is_file():shutil.copy2(f,b/f.name)
shutil.copy2('prepare_round25.py',b/'prepare_round25.py')
shutil.copy2('package_round25.py',b/'package_round25.py')
timings=[json.loads((b/f'timing{k}.json').read_text()) for k in [0,5669,49999]]
assert all(t['success'] for t in timings)
wall=sum(t['total_wall_seconds'] for t in timings)
cpu=sum(r['cpu_seconds'] for t in timings for r in t['modules'])
peak=max(r['peak_rss_kib'] for t in timings for r in t['modules'])/1024**2
rows='\n'.join(f"Cell {t['cell']:5d}: {t['total_wall_seconds']:.2f} s wall; "+f"{sum(r['cpu_seconds'] for r in t['modules']):.2f} s CPU; "+f"{max(r['peak_rss_kib'] for r in t['modules'])/1024**2:.2f} GiB peak RSS" for t in timings)
now=datetime.datetime.now(datetime.timezone.utc)
report=f'''FOUR-VALUE LEAN PROOF — ROUND 25
End-to-end certificate batch

RESULT
The requested batch milestone is complete. Three actual cells of the 50,000-cell
certificate are kernel-verified from concrete numerical witnesses through the
whole-cell real inequality, for every one of the 42 knots:
  k = 0:     [0, 0.0001], with y > 0;
  k = 5669:  [0.5669, 0.5670];
  k = 49999: [4.9999, 5].
Cell 5669 attains the stored final-knot grid bound; the other two exercise the
small-height endpoint and the boundary with the infinite-tail argument.
This is 3/50,000 cells, not a full numerical certificate or the final irrationality
theorem. No full-grid numerical assumption appears in these three cell proofs.

FORMAL STATEMENT
OddZeta.FourValue.Batch.selected_cells_bound takes k in [0,5669,49999], m <= 41,
y > 0, k/10000 <= y <= (k+1)/10000, and proves
  certificateG y - 2*pi*y
    + basisKnot m * analyticBasisPotential (basisKnotWeight m)
        ((normalizedContourPoint y)^2)
  <= Numerical.height m.
The combined theorem applies the three concrete CellCertificate instances and
the proved general cell_certificate_sound theorem. The saved key_statements.txt
contains Lean's exact type. All 126 cell/knot combinations hold throughout their
respective intervals, not merely at finitely sampled heights.

WHAT LEAN CHECKS
For each cell, 46 logarithm and 24 arctangent scalar enclosures establish the
stored G ceiling, including entropy normalization and the cell slope allowance.
All 45 centers have exact rational squared-distance checks at both endpoints,
for the center and its complex conjugate: 180 endpoint checks per cell. The
square-root ceiling candidates are nonnegative and at least 1/50.
A further 90 logarithm evaluations establish the 45 stored K ceilings, including
the 17/5,000,000,000 curvature allowance. Exact rational checks then establish
all 42 weighted knot inequalities against the committed height table.
The general interpolation lemmas propagate those bounds across the whole cell.

Arb at 256-bit precision generates scalar endpoint candidates; rational integer
square roots generate distance candidates. These external computations are not
trusted proof steps. Every candidate and finite inequality is checked by Lean,
using the formally sound integer interval evaluator and decide +kernel. The
interval scale is 2^80, logarithm series length 24, arctangent length 32, and
logarithm reduction fuel 64. The verified Machin enclosure supplies pi.
The G/K integers come from the existing Round 7 replay arrays. Centers, knot
weights, and target heights come from the already committed Lean tables.

MEASURED PERFORMANCE (SEQUENTIAL CELL BUILDS)
{rows}
Total: {wall:.2f} seconds wall, {cpu:.2f} seconds CPU; peak {peak:.2f} GiB.
These are single-run end-to-end module compilations, including imports, proof
elaboration, kernel checking and assembly. Shared-tool compilation, witness
generation, final combined theorem and cumulative audit are excluded. See the
JSON and logs in numerical/batch25. Lean profiler categories overlap and are
not independent elapsed times.

The batch exposed costs missed by the earlier evaluator-only benchmark. Naively
repeating this per-cell layout over 50,000 cells gives about
{wall/3*50000/3600:.0f} single-worker wall-hours ({wall/3*50000/86400:.1f} days), or
{cpu/3*50000/3600:.0f} CPU-hours. This is a mechanical extrapolation from only three
selected cells, not a validated forecast. It includes repeated imports and
scalar-proof assembly that larger batches could share. The earlier 1–3 day
whole-stage estimate is not supported by the current per-cell implementation.
The fast evaluator alone is insufficient to estimate full-certificate runtime.

Before a full-grid run, the useful next work is shared constant enclosures,
integer/sparse weighted-knot checks, and batched assembly with controlled memory.
The full grid may also contain harder precision or ceiling cases not exercised
here. No additional precision was needed for this three-cell batch.

IMPLEMENTATION FINDINGS
Direct expansion of complex-distance and weight tables was replaced by finite
rational checks and reusable soundness lemmas. K bounds now check logarithm
pairs directly, avoiding redundant separately elaborated scalar lemmas.
Some assembly attempts stalled while reconciling rational-to-real casts and
nonzero cell-width expressions; explicit cast normalization and a proved width
identity resolved those issues. One intermediate second-cell process ended
without a timing receipt; the final complete successful rerun is authoritative.
Aborted/failed diagnostic logs are retained and clearly excluded from success
claims. Final generated sources reproduce from the saved witness generator.

AUDIT AND PRESERVATION
{v['new_theorem_count']} new theorem declarations in {v['new_module_count']} modules.
{v['theorem_count']} cumulative audited declarations in {v['substantive_module_count']} substantive modules.
The full Lake build and every-declaration axiom audit passed. Only propext,
Classical.choice and Quot.sound are allowed. No sorry, admit, native_decide or
custom axiom occurs. All 221 Round 24 substantive Lean modules are byte-for-byte
unchanged. Exact source hashes and audit outputs are included.
Lean: {v['toolchain']}
Mathlib: {v['mathlib_commit']}
Checkpoint: {now.isoformat()}

REMAINING OBLIGATIONS
The full GridCertificate 50000 is still uninstantiated. The other 49,997 cells
must be certified and assembled before applying finite_certificate_of_grid.
The global arithmetic lower bound and final contradiction also remain.
No unconditional irrationality theorem for zeta(7), zeta(9), zeta(11), zeta(13)
is claimed. No process is left running after this checkpoint.

REPRODUCTION
Restore the pinned Lean/mathlib dependencies and run lean/verify.sh. Committed
Lean sources suffice for verification. Optional witness regeneration and timing
commands are in numerical/batch25/README.txt. The archive is cumulative; runtime
binaries and .lake caches are excluded. See SHA256_MANIFEST.txt for file hashes.
'''
name='Four_Value_Lean_Batch_Report_2026-10-14.txt';(root/name).write_text(report);(p/'README.txt').write_text(report)
(root/'README.txt').write_text('Four-value Lean proof, Round 25\n\nEnd-to-end three-cell certificate batch complete; full numerical certificate remains incomplete.\nRead '+name+'.\n')
(root/'process_status.json').write_text(json.dumps({'round':25,'checkpoint_time':now.isoformat(),'end_to_end_certificate_batch_verified':True,'certified_cells':[0,5669,49999],'total_grid_cells':50000,'numerical_stage_complete_in_lean':False,'full_four_value_zeta_theorem_verified':False,'remaining':['Full concrete grid certificate','global arithmetic lower bound','final contradiction']},indent=2)+'\n')
files=sorted(f for f in root.rglob('*') if f.is_file() and '.lake' not in f.parts and '__pycache__' not in f.parts and f.name!='SHA256_MANIFEST.txt')
(root/'SHA256_MANIFEST.txt').write_text(''.join(hashlib.sha256(f.read_bytes()).hexdigest()+'  '+str(f.relative_to(root))+'\n' for f in files))
out=Path('deliverables25');out.mkdir(exist_ok=True);shutil.copy2(root/name,out/name)
zpath=out/'Four_Value_Lean_Round25.zip'
with zipfile.ZipFile(zpath,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for f in files+[root/'SHA256_MANIFEST.txt']:z.write(f,Path('Four_Value_Lean_Round25')/f.relative_to(root))
with zipfile.ZipFile(zpath) as z:assert z.testzip() is None
print(json.dumps({'zip':str(zpath.resolve()),'report':str((out/name).resolve()),'theorems':v['theorem_count'],'modules':v['substantive_module_count'],'wall_seconds':wall,'bytes':zpath.stat().st_size}))
