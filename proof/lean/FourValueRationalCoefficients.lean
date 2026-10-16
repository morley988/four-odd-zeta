import FourValueCoefficientMap

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

theorem centeredDenominator_map (f : K →+* L) (b : ℕ) :
    (centeredDenominator (K:=K) b).map f = centeredDenominator (K:=L) b := by
  induction b with
  | zero => simp [centeredDenominator]
  | succ b ih => simp [centeredDenominator, ih]

theorem targetNormalization_map (f : K →+* L) (n : ℕ) :
    f (targetNormalization (K:=K) n) = targetNormalization (K:=L) n := by
  simp [targetNormalization]

theorem coefficientRatFuncMap_C (f : K →+* L) (a : K) :
    coefficientRatFuncMap f (RatFunc.C a) = RatFunc.C (f a) := by
  simpa using coefficientRatFuncMap_polynomial f (C a)

theorem coefficientRatFuncMap_X (f : K →+* L) :
    coefficientRatFuncMap f RatFunc.X = RatFunc.X := by
  simpa using coefficientRatFuncMap_polynomial f X

theorem tupleRationalTest_map (f : K →+* L) (b : ℕ) (a : Fin 15 → ℕ) (p : K[X]) :
    coefficientRatFuncMap f (tupleRationalTest b a p) =
      tupleRationalTest b a (p.map f) := by
  simp [tupleRationalTest, tupleWeight, coefficientRatFuncMap_fraction,
    coefficientRatFuncMap_polynomial, tupleNumerator, tupleDenominator,
    Polynomial.map_prod, centeredDenominator_map, Polynomial.map_comp,
    coefficientRatFuncMap_C, coefficientRatFuncMap_X, map_ofNat]

theorem finiteHarmonic_map (f : K →+* L) (m s : ℕ) :
    f (finiteHarmonic (K:=K) m s) = finiteHarmonic (K:=L) m s := by
  simp [finiteHarmonic]

theorem rationalB_map (f : K →+* L) (b k : ℕ) (r : RatFunc K) :
    rationalB b k (coefficientRatFuncMap f r) = f (rationalB b k r) := by
  simp only [rationalB, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simpa using rationalCoefficientAt_map f (j:K) (-(k:ℤ)) r

theorem rationalC_map (f : K →+* L) (b h : ℕ) (r : RatFunc K) :
    rationalC b h (coefficientRatFuncMap f r) = f (rationalC b h r) := by
  simp only [rationalC, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    map_mul, map_neg, map_pow, map_one, map_sum, map_natCast, finiteHarmonic_map]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  simpa using rationalCoefficientAt_map f (j:K) (-((k+1:ℕ):ℤ)) r

theorem nineRationalObservations_map (f : K →+* L) (b : ℕ) (i : Fin 9) (r : RatFunc K) :
    nineRationalObservations b i (coefficientRatFuncMap f r) =
      f (nineRationalObservations b i r) := by
  fin_cases i <;> simp [nineRationalObservations, rationalB_map, rationalC_map]

theorem normalizedTargetFunctional_map (f : K →+* L) (n : ℕ) (i : Fin 9) (p : K[X]) :
    normalizedTargetFunctional n i (p.map f) = f (normalizedTargetFunctional n i p) := by
  simp only [normalizedTargetFunctional, LinearMap.comp_apply, normalizedTupleTest,
    LinearMap.smul_apply, map_smul, smul_eq_mul, map_mul, targetNormalization_map]
  rw [← tupleRationalTest_map f, nineRationalObservations_map]

theorem squareRootProduct_map (f : K →+* L) (i : ℕ) :
    (squareRootProduct (K:=K) i).map f = squareRootProduct (K:=L) i := by
  simp [squareRootProduct, linearRootProduct, List.map_map, Polynomial.map_list_prod,
    Function.comp_def]

theorem squareBasisPolynomial_map (f : K →+* L) (i : ℕ) :
    (squareBasisPolynomial (K:=K) i).map f = squareBasisPolynomial (K:=L) i := by
  by_cases hi : i=0 <;> simp [squareBasisPolynomial, hi, squareRootProduct_map, map_ofNat]

/-- Rational model of the checked physical-coordinate observations. -/
def rationalPhysicalFunctional (n : ℕ) (i : Fin 9) : ℚ[X] →ₗ[ℚ] ℚ where
  toFun p := normalizedTargetFunctional n i (p.comp (C 4*X))
  map_add' p q := by simp [Polynomial.add_comp]
  map_smul' c p := by simp [Polynomial.smul_comp]

theorem physicalTargetFunctional_ratCast (n : ℕ) (i : Fin 9) (p : ℚ[X]) :
    physicalTargetFunctional n i (p.map (algebraMap ℚ ℂ)) =
      (rationalPhysicalFunctional n i p : ℂ) := by
  change normalizedTargetFunctional n i ((p.map _).comp (C 4*X)) = _
  have h := normalizedTargetFunctional_map (algebraMap ℚ ℂ) n i (p.comp (C 4*X))
  convert h using 1 <;> try rfl
  congr 1
  rw [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  norm_num

def rationalFourValueFunctional (n : ℕ) (lambda : Fin 4 → ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  rationalPhysicalFunctional n 8 + lambda 0 • rationalPhysicalFunctional n 0 +
    lambda 1 • rationalPhysicalFunctional n 1 + lambda 2 • rationalPhysicalFunctional n 2 +
    lambda 3 • rationalPhysicalFunctional n 3

theorem fourValuePencil_ratCast (n : ℕ) (lambda : Fin 4 → ℚ) (p : ℚ[X]) :
    fourValuePencil n (fun i => (lambda i : ℂ)) (p.map (algebraMap ℚ ℂ)) =
      (rationalFourValueFunctional n lambda p : ℂ) := by
  simp [fourValuePencil_apply, physicalTargetFunctional_ratCast,
    rationalFourValueFunctional]

/-- The actual rational coefficient matrix, with the same square basis. -/
def rationalFourValueMatrix (n : ℕ) (lambda : Fin 4 → ℚ) :
    Matrix (Fin (targetHankelDegree n+1)) (Fin (targetHankelDegree n+1)) ℚ :=
  squareBasisGram (rationalFourValueFunctional n lambda) (targetHankelDegree n)

theorem rationalFourValueMatrix_cast (n : ℕ) (lambda : Fin 4 → ℚ) :
    (rationalFourValueMatrix n lambda).map (algebraMap ℚ ℂ) =
      squareBasisGram (fourValuePencil n (fun i => (lambda i:ℂ))) (targetHankelDegree n) := by
  ext i j
  change (rationalFourValueFunctional n lambda
    (squareBasisPolynomial i.val*squareBasisPolynomial j.val):ℂ) = _
  rw [← fourValuePencil_ratCast]
  simp [squareBasisGram, Polynomial.map_mul, squareBasisPolynomial_map]

/-- Rationality of the four classical zeta values produces the very same
matrix of derivative series as the preceding analytic identification. -/
theorem classicalZetaSeriesMatrix_rational (n : ℕ) (z : Fin 4 → ℚ)
    (hz : ∀ i : Fin 4, riemannZeta ((![7,9,11,13] : Fin 4 → ℂ) i) = (z i:ℂ)) :
    classicalZetaSeriesMatrix n =
      (rationalFourValueMatrix n (fun i => (![15,70,210,495] : Fin 4 → ℚ) i*z i)).map
        (algebraMap ℚ ℂ) := by
  rw [rationalFourValueMatrix_cast, classicalZetaSeriesMatrix_eq]
  congr 1
  unfold classicalZetaFunctional
  congr 1
  funext i
  fin_cases i <;> simp [classicalZetaPencilCoefficients, ← hz]

/-- The selected minor is a nonzero rational number, not a separately
postulated arithmetic witness. -/
theorem rationalFourValueMatrix_nonzero_minor (n : ℕ) (hn : 1≤n) (lambda : Fin 4 → ℚ) :
    ∃ rows cols : Fin (targetHankelDegree n+1-4) ↪ Fin (targetHankelDegree n+1),
      ((rationalFourValueMatrix n lambda).submatrix rows cols).det ≠ 0 := by
  obtain ⟨rows, cols, h⟩ := (fourValue_uniform_nonvanishing n hn
    (fun i => (lambda i:ℂ))).2
  refine ⟨rows, cols, ?_⟩
  intro hz
  rw [← rationalFourValueMatrix_cast] at h
  apply h
  rw [show ((rationalFourValueMatrix n lambda).map (algebraMap ℚ ℂ)).submatrix rows cols =
    ((rationalFourValueMatrix n lambda).submatrix rows cols).map (algebraMap ℚ ℂ) from rfl,
    ]
  simpa only [hz, map_zero, RingHom.mapMatrix_apply] using ((algebraMap ℚ ℂ).map_det
    ((rationalFourValueMatrix n lambda).submatrix rows cols)).symm
end OddZeta.FourValue
