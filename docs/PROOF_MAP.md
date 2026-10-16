# Proof map

All module paths below are relative to `proof/lean/`. Refer to the manuscript for definitions and historical references.

| Mathematical step | Entry point |
|---|---|
| Pearson identities and seed independence | `FourValueSeedIndependence.lean` |
| Uniform rank and selected nonzero minor | `FourValueUniformNonvanishing.lean` |
| Corrected-coordinate zeta identity | `FourValueCorrectedZeta.lean` |
| Matrix and determinant identification | `FourValueCorrectedAssembly.lean` |
| Uniform analytic estimate and error | `FourValueNumericalBridge.lean` |
| Analytic finite certificate | `FourValueFullGrid.lean` |
| Local-to-global valuation inequality | `FourValueGlobalCosts.lean` |
| Rational arithmetic cells and boxes | `FourValueArithmeticCertificate.lean` |
| Weighted prime sums and product formula | `FourValueGlobalPrimeSum.lean` |
| Eventual arithmetic lower rate | `FourValueGlobalArithmeticRate.lean` |
| Selected rational minor under rationality | `FourValueGlobalArithmeticLower.lean` |
| Final contradiction with explicit hypotheses | `FourValueFinalContradiction.lean` |
| Supplied-certificate conclusion | `FourValueFinal.lean` |
| Axiom dependency audit | `FinalAxiomAudit.lean` |

The Pearson coordinate `X=4Y` must not be confused with the analytic/arithmetic basis coordinate `Y=x²`. The corrected-coordinate transfer is essential to comparing the same determinant on both sides.

This is a guide to entry points, not a complete dependency graph. Historical and experimental modules are preserved for provenance; the reproduction script specifies the final dependency targets.
