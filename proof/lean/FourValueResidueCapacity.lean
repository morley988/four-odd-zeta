import FourValueSelectedSingleNode

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- Number of surviving denominator factors in one signed residue class. -/
def targetResidueCapacity (p n : ℕ) (r : ℤ) : ℕ :=
  ((targetPoleList n).filter (fun t => (p:ℤ)∣r-t)).length

theorem targetResidueCapacity_count (n : ℕ) (r : ℤ) :
    (targetResidueCapacity p n r:ℤ) =
      ∑ i : Fin 10,centeredResidueCount p r (targetFactorialEndpoints i*n) := by
  simp only [targetResidueCapacity,targetPoleList,List.filter_flatten,List.length_flatten,
    List.map_map,List.map_ofFn,List.sum_ofFn,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [centeredResidueCount_eq_card]
  congr 1
  simp only [Function.comp_apply]
  rw [← List.toFinset_card_of_nodup ((Finset.nodup_toList _).filter _)]
  rw [← List.filter_toFinset]
  simp

theorem targetResidueCapacity_floor (n : ℕ) (r : ℤ) :
    (targetResidueCapacity p n r:ℤ) =
      ∑ i : Fin 10, ((((targetFactorialEndpoints i*n:ℕ):ℤ)+r)/(p:ℤ)+
        (((targetFactorialEndpoints i*n:ℕ):ℤ)-r)/(p:ℤ)+1) := by
  rw [targetResidueCapacity_count]
  apply Finset.sum_congr rfl
  intro i hi
  exact centeredResidueCount_floor _ _

theorem targetPoleList_count_neg (n : ℕ) (a : ℤ) :
    (targetPoleList n).count (-a)=(targetPoleList n).count a := by
  simp only [targetPoleList,List.count_flatten,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Function.comp_apply]
  rw [(Finset.nodup_toList _).count,(Finset.nodup_toList _).count]
  have he : (-a∈poleWindow (targetFactorialEndpoints i*n)) ↔ a∈poleWindow (targetFactorialEndpoints i*n) := by
    simp only [poleWindow,Finset.mem_Icc]
    omega
  simp only [Finset.mem_toList,he]

def targetResidueAnnihilator (p n : ℕ) (r : ℤ) : ℚ[X] :=
  linearRootProduct (((targetPoleList n).filter (fun t => (p:ℤ)∣r-t)).map (fun t : ℤ => 4*(t:ℚ)^2))

theorem targetResidueAnnihilator_monic (n : ℕ) (r : ℤ) :
    (targetResidueAnnihilator p n r).Monic := linearRootProduct_monic _

theorem targetResidueAnnihilator_degree (n : ℕ) (r : ℤ) :
    (targetResidueAnnihilator p n r).natDegree=targetResidueCapacity p n r := by
  simp [targetResidueAnnihilator,linearRootProduct_degree,targetResidueCapacity]
end OddZeta.FourValue
