Historical scaffolding used during development, not a regeneration workflow.
create_sources.py and create_arithmetic_sources.py produced initial drafts that
were subsequently corrected directly in the final Lean source files. Do not run
them over the finished proof. The authoritative files are in lean/.
generate_arithmetic.py produces grid_arithmetic.txt from the original NPZ.
Only verify_grid.py, verify_values.py, and verify_fullgrid.sh are needed to
reproduce verification of the finished checkpoint.
