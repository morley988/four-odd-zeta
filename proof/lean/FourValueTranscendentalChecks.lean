import FourValueTranscendental

noncomputable section
namespace OddZeta.FourValue.Transcendental
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem log_two_enclosure :
    (69314718055994530941/10^20:ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ (69314718055994530942/10^20:ℝ) := by
  have h := log_rat_check 24 2 (69314718055994530941/10^20) (69314718055994530942/10^20)
    (by norm_num) (by norm_num [logRat, sum_range_succ])
    (by norm_num [logRat, sum_range_succ])
  norm_num at h ⊢
  exact h

theorem atan_fifth_enclosure :
    (19739555984988075837/10^20:ℝ) ≤ Real.arctan (1/5) ∧
    Real.arctan (1/5) ≤ (19739555984988075838/10^20:ℝ) := by
  have h := atan_rat_check 16 (1/5) (19739555984988075837/10^20) (19739555984988075838/10^20)
    (by norm_num [atanRat, sum_range_succ]) (by norm_num [atanRat, sum_range_succ])
  norm_num at h ⊢
  exact h

theorem atan_239_enclosure :
    (418407600207472386/10^20:ℝ) ≤ Real.arctan (1/239) ∧
    Real.arctan (1/239) ≤ (418407600207472387/10^20:ℝ) := by
  have h := atan_rat_check 5 (1/239) (418407600207472386/10^20) (418407600207472387/10^20)
    (by norm_num [atanRat, sum_range_succ]) (by norm_num [atanRat, sum_range_succ])
  norm_num at h ⊢
  exact h

theorem pi_machin_enclosure :
    (314159265358979323844/10^20:ℝ) ≤ Real.pi ∧
    Real.pi ≤ (314159265358979323864/10^20:ℝ) := by
  have h := pi_enclosure (19739555984988075837/10^20) (19739555984988075838/10^20)
    (418407600207472386/10^20) (418407600207472387/10^20)
    (by have h := atan_fifth_enclosure.1; norm_num at h ⊢; exact h) (by have h := atan_fifth_enclosure.2; norm_num at h ⊢; exact h)
    (by have h := atan_239_enclosure.1; norm_num at h ⊢; exact h) (by have h := atan_239_enclosure.2; norm_num at h ⊢; exact h)
  norm_num at h ⊢
  exact h

end OddZeta.FourValue.Transcendental
