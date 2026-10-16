# Four odd zeta values

A determinant argument that at least one of **ζ(7), ζ(9), ζ(11), ζ(13)** is irrational.

**Verification status:** the mathematical deduction from explicit finite certificates is checked in Lean. The supplied-certificate theorem uses **eight isolated numerical admissions**, checked externally by exact rational arithmetic and rigorous Arb ball arithmetic. This is **not an admission-free Lean formalization** and has not undergone independent peer review.



## Start here

- [Research manuscript (PDF)](manuscript/Four_Odd_Zeta_Manuscript.pdf) and [LaTeX source](manuscript/Four_Odd_Zeta_Manuscript.tex), with historical context and 21 references.
- [Verification boundary](docs/VERIFICATION.md): what Lean proves, what the numerical programs check, and what remains admitted.
- [Reproduction instructions](docs/REPRODUCING.md), including restoration of compressed certificate tables.
- [Proof map](docs/PROOF_MAP.md) linking the argument to formal modules.
- [Final report](proof/Four_Value_Final_Report_2026-10-15.txt) and [recorded final audit](proof/numerical/final29/verification.json).
- [Provenance and contribution notes](docs/PROVENANCE.md), [publication decisions](docs/PUBLICATION.md), and [change log](CHANGELOG.md).

## The argument

Under simultaneous rationality, a uniform rank argument selects a nonzero rational determinant. The arithmetic lower rate is **−11.52**, while the analytic upper rate is **−11.55706678**, both normalized by `(100n)²`. Their gap is **0.03706678**. The uniform analytic error is `o(n²)`, giving a contradiction for sufficiently large `n`.

The conclusion does not identify an individual irrational value or establish a three-value assertion.

## Quick start

With Python 3 installed:

```sh
python3 scripts/restore_certificates.py
python3 scripts/check_package.py
```

These commands restore and hash-check the package; they do **not** prove the numerical inequalities or rerun Lean. To reproduce the full checks, install the Lean toolchain recorded in `proof/lean/lean-toolchain`, then:

```sh
python3 -m pip install -r requirements.txt
cd proof
bash numerical/final29/reproduce.sh
```

See [REPRODUCING.md](docs/REPRODUCING.md) for the required dependencies, scope of each check, and expected outputs. Linux is the primary reproduction environment; on Windows use WSL for the Bash workflow.

## Repository organization

`proof/` preserves the internal paths and bytes of the completed Round 29 package. `manuscript/` contains the updated exposition. `certificates/` contains losslessly compressed, split copies of two large data tables. `scripts/` provides restoration and integrity checks. No Lean build cache is committed.

The historical Round 29 build reused compiled artifacts. A new clean-checkout build is not claimed merely because the files have been imported into GitHub. Automated workflow results must be read separately from the historical audit.

## Author and contributions

This is the result of an AI & Lean experiment carried out by Morley Davidson using GPT6 Astra on Extra High for ALL research and writing. This follows an earlier corresponding result for nine odd zeta values. Whereas the earlier result was verified fully in Lean, in the current experiment millions of auxiliary numerical checks are not validated through Lean (too slow...) but instead by rational and/or high-precision calculation.

## Citation and licensing

Original code is licensed under the [MIT License](LICENSE-MIT). The manuscript and original documentation are licensed under [CC BY 4.0](LICENSE-CC-BY-4.0). See [Licensing](LICENSE.md) for scope and attribution requirements. Use a specific commit when referring to this development version. A formal `CITATION.cff` and release tag will be added after the bibliographic details are confirmed. Third-party dependencies retain their own licenses and notices.
