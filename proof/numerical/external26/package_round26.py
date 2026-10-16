from pathlib import Path
import json,hashlib,zipfile,shutil,datetime
root=Path('work/Four_Value_Lean_Round20');p=root/'lean';b=root/'numerical/external26'
v=json.loads((p/'external_verification.json').read_text())
assert v['status']=='PASS_WITH_EXPLICIT_EXTERNAL_NUMERICAL_ASSUMPTIONS'
assert v['explicit_assumption_count']==2 and v['core_declarations_unchanged_and_without_sorryAx']==1669
assert not v['fully_lean_certified'] and not v['full_grid_certificate_assembled']
for f in Path('external26').iterdir():
 if f.is_file() and f.name not in ['transcendental_values.txt','verification.json','assumption_audit.json']:
  shutil.copy2(f,b/f.name)
shutil.copy2('package_round26.py',b/'package_round26.py')
initial=json.loads((b/'initial_verification.json').read_text());final=v['numerical_verification']
assert initial['sha256']==final['sha256']
now=datetime.datetime.now(datetime.timezone.utc)
locations=', '.join(str(x['line']) for x in v['source_audit']['locations'])
report=f'''FOUR-VALUE ZETA PROJECT — ROUND 26
Externally checked transcendental values and isolated Lean assumptions

COMPLETED
Exported and independently checked every scalar transcendental range for the
entire 50,000-cell grid: 5,700,022 logarithm ranges and 1,200,000 arctangent ranges,
6,900,022 total. The isolated ASCII text file is 400,205,372 bytes. Each row gives
an exact positive rational argument p/q and lower numerator m, with endpoints
m/10^18 and (m+5)/10^18. All bounds therefore have width 5*10^-18.
There are 22 shared constant logs, then 114 logs and 24 arctangents per cell.

The standalone checker uses Arb via python-flint 0.9.0, at 256-bit precision.
It recomputes each value from the text's exact rational argument and requires
strict containment of the entire outward-rounded Arb ball in the claimed range.
No sampling, rounded-float comparison, or generator result is accepted as proof
of containment. The first full run passed in {initial['seconds']:.2f} seconds;
the final audit rerun passed in {final['seconds']:.2f} seconds. Hardware-dependent
single-run times are not promises for another machine. The generator took about
95 seconds at 192-bit precision. The checker is independently runnable, though
it uses the same Arb library as the generator rather than a second arithmetic
implementation. Deliberately false-bound and truncated-file tests were rejected.

EXACT TRUST BOUNDARY
Only lean/FourValueExternalTranscendental.lean contains admitted proofs.
There are exactly TWO marked blocks, at source lines {locations}:
  log_values : the finite family indexed by Fin 5700022;
  atan_values : the finite family indexed by Fin 1200000.
Both statements assert lower <= log/arctan(argument) <= upper for actual table
rows. Neither asserts bounds for arbitrary arguments or arbitrary intervals.
Two proof blocks cover 6,900,022 scalar range claims; these are different counts.

The common marker suffix is EXTERNAL_TRANSCENDENTAL_VALUE_CERTIFICATION_V1.
The source audit constructs the full statement match, counts exactly two, checks
that every source token is on those lines, verifies the expected theorem blocks,
and rejects extra admissions/custom axioms/native_decide throughout the project.
No admission of the full grid certificate, arithmetic lower bound, nonvanishing,
or final irrationality theorem has been introduced.

The same text file is embedded as immutable Lean data by an elaborator that
constructs ordinary safe definitions, not proof terms. Chunking and named data
blocks control build memory. The data definitions have no additional axioms;
rational arithmetic retains standard propext/Classical.choice/Quot.sound.
The table itself has no axiom dependencies. The two theorem blocks are the sole
new numerical trust boundary. Its exact content hash is
{final['sha256']}.
The conditional verification script pins that hash and reruns the independent
numerical checker, so an altered table cannot silently reuse the saved receipt.

INTEGRATION STATUS
FourValueExternalInterface imports the proved core and the isolated assumption
file and supplies log_bound_of_row / atan_bound_of_row. These transfer a selected
row to desired rational constants once the argument and endpoint equalities are
proved. The old fully certified three-cell batch is retained unchanged.

Full-grid assembly is NOT complete. Identifying all rows with the analytic grid
expressions and completing the G/K, distance, and weighted-knot arithmetic are
still obligations. No blanket certificate assumption hides them. Exploratory
concrete lookup-proof attempts exceeded the 8 GiB environment limit; they are
not claimed as successful proofs. The final generic interface builds and keeps
row-identification equalities explicit. Further batching or separately audited
external treatment of calculation-only equalities remains implementation work.

AUDIT RESULT
The conditional Lake build and axiom audit passed. All 1,669 original theorem
declarations remain byte-for-byte sourced from Round25 and free of sorryAx.
All original Round25 Lean source files remain unchanged. The new audit covers
1,677 declarations: the original 1,669, four new theorems (two admitted families
and two proved adapters), and four data/decoder definitions. Exactly the four
new theorems depend on sorryAx. No other new axiom dependency is allowed.

This is explicitly a Lean proof interface CONDITIONAL on externally checked
numerical statements. It is not a fully kernel-certified numerical certificate,
and the full four-value irrationality theorem remains unfinished. The unchanged
strict verify.sh still rejects any admitted proofs; use verify_external.sh for
this deliberately conditional variant. No audit result relabels it unconditional.

REVISED TIME ESTIMATE AFTER THIS CHECKPOINT
Assuming later calculation-only steps receive similarly isolated, independently
checked treatment, a provisional remaining budget is about 25–70 hours of active
work. The components are approximately:
  full-grid data linkage and remaining numerical/arithmetic interfaces: 3–10 h;
  global arithmetic allocation and prime-sum lower bound: 12–36 h;
  final analytic/arithmetic contradiction and theorem integration: 4–12 h;
  final conditional audit, cleanup and reproducibility: 2–6 h.
The component total is 21–64 h; 25–70 h allows a modest integration margin.
The global arithmetic proof remains the largest mathematical uncertainty and
could exceed that range if a genuine obstruction appears. This is a planning
estimate, not a measured completion forecast or upper bound.

The former ~30-day figure was the naive serial cost of the old per-cell Lean
implementation. Under the requested external-calculation policy it is no longer
the appropriate numerical-work estimate: the entire log/arctan checking run
already took about half a minute. Merely replacing the transcendental checks
would not automatically remove all other per-cell proof-assembly costs; the
revised estimate explicitly assumes the analogous treatment of later purely
calculational checks that the user proposed. Mathematical arguments remain
proof obligations and are not silently admitted.

REPRODUCTION
The standalone Python program and text file suffice for independent checking.
Install python-flint==0.9.0 and run:
  python verify_values.py transcendental_values.txt --report verification.json
Optional: --precision 512, or --sha256 followed by the hash above.
For the cumulative conditional Lean audit, restore the pinned dependencies and
run lean/verify_external.sh. Detailed format and commands are in
numerical/external26/README.txt. Sources, logs, negative controls, original core
and both prior/full conditional audit evidence are included. Runtime binaries
and .lake caches are excluded. No worker remains running after this checkpoint.
Checkpoint: {now.isoformat()}
'''
name='Four_Value_External_Numerics_Report_2026-10-14.txt';(root/name).write_text(report)
(root/'README.txt').write_text('Four-value Lean proof, Round 26: explicit external numerical assumptions\n\nRead '+name+' and numerical/external26/README.txt.\nUse lean/verify_external.sh for the conditional variant; the strict audit remains unchanged.\nFull grid assembly and the final theorem remain incomplete.\n')
(root/'process_status.json').write_text(json.dumps({'round':26,'checkpoint_time':now.isoformat(),'all_grid_transcendental_values_externally_verified':True,'scalar_bounds':6900022,'explicit_admitted_proofs':2,'fully_lean_certified':False,'full_grid_certificate_assembled':False,'full_four_value_zeta_theorem_verified':False,'remaining':['Full grid linkage and remaining finite arithmetic checks','global arithmetic lower bound','final contradiction and conditional audit']},indent=2)+'\n')
files=sorted(f for f in root.rglob('*') if f.is_file() and '.lake' not in f.parts and '__pycache__' not in f.parts and f.name!='SHA256_MANIFEST.txt')
(root/'SHA256_MANIFEST.txt').write_text(''.join(hashlib.sha256(f.read_bytes()).hexdigest()+'  '+str(f.relative_to(root))+'\n' for f in files))
out=Path('deliverables26');out.mkdir(exist_ok=True)
for f in [root/name,b/'transcendental_values.txt',b/'verify_values.py',p/'FourValueExternalTranscendental.lean']:
 shutil.copy2(f,out/f.name)
zpath=out/'Four_Value_Lean_Round26.zip'
with zipfile.ZipFile(zpath,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for f in files+[root/'SHA256_MANIFEST.txt']:z.write(f,Path('Four_Value_Lean_Round26')/f.relative_to(root))
with zipfile.ZipFile(zpath) as z:assert z.testzip() is None
print(json.dumps({'zip':str(zpath.resolve()),'zip_bytes':zpath.stat().st_size,'report':str((out/name).resolve()),'rows':6900022,'explicit_assumptions':2}))
