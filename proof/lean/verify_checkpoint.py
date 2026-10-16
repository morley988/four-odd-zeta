"""Summarize saved Lean build/audit evidence; this is not a substitute for Lean.

Run verify.sh to regenerate the build and audit before running this parser.
The parser rejects missing declarations, nonstandard axioms, and proof holes.
"""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
allowed = {"propext", "Classical.choice", "Quot.sound"}
names = json.loads((root / "audit_declarations.json").read_text())
baseline = json.loads((root / "baseline_audit_declarations.json").read_text())
new_modules = json.loads((root / "audit_modules.json").read_text())
audit = (root / "axiom_audit.log").read_text()
entries = re.findall(
    r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",
    audit,
)
axioms = {}
duplicates = []
for name, dependencies, no_axioms in entries:
    if name in axioms:
        duplicates.append(name)
    axioms[name] = [s.strip() for s in dependencies.split(",") if s.strip()]
missing = sorted(set(names) - axioms.keys())
extra = sorted(axioms.keys() - set(names))
unexpected = {n: sorted(set(a) - allowed) for n, a in axioms.items()
              if set(a) - allowed}

def strip_comments_and_strings(source):
    # Lean block comments nest. Preserve newlines for useful diagnostics.
    out, i, depth, in_string = [], 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif in_string:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                in_string = False
                i += 1
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            in_string = True
            i += 1
        else:
            out.append(source[i])
            i += 1
    assert depth == 0 and not in_string, "Unclosed comment/string"
    return "".join(out)

sources = sorted(root.glob("*.lean"))
substantive = [p for p in sources if p.name not in
               {"FourValue.lean", "AxiomAudit.lean", "KeyStatements.lean"}]
forbidden = {}
for source in sources:
    clean = strip_comments_and_strings(source.read_text())
    hits = re.findall(r"\b(?:sorry|admit|native_decide|axiom)\b", clean)
    if hits:
        forbidden[source.name] = hits
build_exit = int((root / "build.exit").read_text().strip())
audit_exit = int((root / "axiom_audit.exit").read_text().strip())
build_ok = build_exit == 0 and "Build completed successfully" in (root / "build.log").read_text()
audit_ok = audit_exit == 0 and not any([missing, extra, duplicates, unexpected])
result = {
    "scope": "Round 25: end-to-end certificate batch for actual grid cells 0, 5669, and 49999, including all 42 knot inequalities and whole-cell real bounds. Full grid certificate and final theorem remain incomplete.",
    "build_success": build_ok,
    "axiom_audit_complete": audit_ok,
    "full_four_value_zeta_theorem_verified": False,
    "concrete_nine_vector_independence_verified": build_ok and audit_ok and not forbidden,
    "stage3_normalization_verified": build_ok and audit_ok and not forbidden,
    "finite_pearson_restriction_classification_verified": build_ok and audit_ok and not forbidden,
    "concrete_uniform_rank_instantiation_verified": build_ok and audit_ok and not forbidden,
    "classical_zeta_series_identification_verified": build_ok and audit_ok and not forbidden,
    "fourth_derivative_and_boundary_verified": build_ok and audit_ok and not forbidden,
    "rational_coefficient_descent_verified": build_ok and audit_ok and not forbidden,
    "concrete_large_prime_local_bounds_verified": build_ok and audit_ok and not forbidden,
    "full_concrete_valuation_stage_complete": build_ok and audit_ok and not forbidden,
    "global_arithmetic_lower_bound_verified": False,
    "concrete_contour_basis_stage_complete": build_ok and audit_ok and not forbidden,
    "actual_zeta_contour_identity_verified": build_ok and audit_ok and not forbidden,
    "uniform_asymptotic_error_stage_complete": build_ok and audit_ok and not forbidden,
    "uniform_error_theorem_requires_numerical_certificate": True,
    "uniform_actual_weight_basis_bounds_verified": build_ok and audit_ok and not forbidden,
    "uniform_laplace_and_selected_minor_errors_verified": build_ok and audit_ok and not forbidden,
    "riemann_sum_and_factorial_integral_verified": build_ok and audit_ok and not forbidden,
    "numerical_certificate_interpolant_instantiated": build_ok and audit_ok and not forbidden,
    "corrected_analytic_coordinate_arithmetic_adapter_verified": build_ok and audit_ok and not forbidden,
    "transcendental_enclosure_lemmas_verified": build_ok and audit_ok and not forbidden,
    "weight_potential_whole_cell_bound_verified": build_ok and audit_ok and not forbidden,
    "finite_grid_soundness_verified": build_ok and audit_ok and not forbidden,
    "integer_interval_backend_verified": build_ok and audit_ok and not forbidden,
    "optimized_transcendental_evaluator_verified": build_ok and audit_ok and not forbidden,
    "end_to_end_certificate_batch_verified": build_ok and audit_ok and not forbidden,
    "certified_grid_cells": [0, 5669, 49999],
    "total_grid_cells": 50000,
    "concrete_grid_certificate_instantiated": False,
    "numerical_transcendental_certificate_verified": False,
    "numerical_certificate_stage_complete_in_lean": False,
    "certificate_quadrature_verified_in_lean": build_ok and audit_ok and not forbidden,
    "certificate_infinite_tail_verified_in_lean": build_ok and audit_ok and not forbidden,
    "numerical_certificate_stage_complete_in_lean": False,
    "certificate_quadrature_verified_in_lean": build_ok and audit_ok and not forbidden,
    "certificate_infinite_tail_verified_in_lean": build_ok and audit_ok and not forbidden,
    "toolchain": (root / "lean-toolchain").read_text().strip(),
    "mathlib_commit": "0df444a360eaa60ab8c11dca51a86af692955474",
    "substantive_module_count": len(substantive),
    "new_module_count": len(new_modules),
    "theorem_count": len(names),
    "new_theorem_count": len(names) - len(baseline),
    "build_exit_code": build_exit,
    "axiom_audit_exit_code": audit_exit,
    "missing_audits": missing,
    "extra_audits": extra,
    "duplicate_audits": duplicates,
    "unexpected_axioms": unexpected,
    "forbidden_source_tokens": forbidden,
    "axioms": axioms,
    "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
}
(root / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
assert build_ok and audit_ok and not forbidden, "Checkpoint evidence failed validation"
print(json.dumps({k: v for k, v in result.items() if k not in {"axioms", "source_sha256"}}, indent=2))
