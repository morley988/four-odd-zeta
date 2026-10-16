import FourValuePrimePowerCounts

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem squareRootProduct_succ (i : ℕ) :
    squareRootProduct (K:=K) (i+1)=squareRootProduct i*(X-C ((i:K)^2)) := by
  simp [squareRootProduct,List.range_succ,linearRootProduct,List.map_append,List.prod_append]

theorem squareRootProduct_square_comp (j : ℕ) :
    (squareRootProduct (K:=K) (j+1)).comp (X^2)=X*centeredDenominator j := by
  induction j with
  | zero => simp [squareRootProduct,linearRootProduct,centeredDenominator]; ring
  | succ j ih =>
    rw [squareRootProduct_succ,mul_comp,ih]
    simp only [sub_comp,X_comp,C_comp,centeredDenominator]
    simp only [map_pow]
    ring

theorem squareBasis_physical_factorization (j : ℕ) :
    ((squareBasisPolynomial (K:=K) (j+1)).comp (C 4*X)).comp (X^2) =
      C (2/((2*(j+1)).factorial:K))*(C 2*X)*
        ((centeredDenominator j).comp (C 2*X)) := by
  simp only [squareBasisPolynomial,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,
    mul_comp,C_comp]
  have he : C (4:K)*X^2=(X^2).comp (C 2*X) := by
    simp only [pow_comp,X_comp,mul_pow,← map_pow]
    norm_num
  rw [comp_assoc,mul_comp,C_comp,X_comp,he,← comp_assoc,squareRootProduct_square_comp,mul_comp,X_comp]
  ring
end OddZeta.FourValue
