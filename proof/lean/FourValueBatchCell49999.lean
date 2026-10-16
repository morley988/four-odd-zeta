import FourValueBatchEnclosures49999

noncomputable section
namespace OddZeta.FourValue.Batch.Cell49999
open OddZeta.FourValue.Transcendental
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true

def Uq (j : Fin 45) : ℚ := [((412383425953/10000000000):ℚ), ((205981681693/5000000000):ℚ), ((25743138131/625000000):ℚ), ((41152720731/1000000000):ℚ), ((411453766487/10000000000):ℚ), ((411429331911/10000000000):ℚ), ((82200244173/2000000000):ℚ), ((102744172813/2500000000):ℚ), ((410532562529/10000000000):ℚ), ((102626984663/2500000000):ℚ), ((410047780943/10000000000):ℚ), ((410023063567/10000000000):ℚ), ((409546865739/10000000000):ℚ), ((409522055617/10000000000):ℚ), ((25564362919/625000000):ℚ), ((409004904583/10000000000):ℚ), ((102124148447/2500000000):ℚ), ((102117900101/2500000000):ℚ), ((407947217091/10000000000):ℚ), ((407922133173/10000000000):ℚ), ((101845416717/2500000000):ℚ), ((25459780821/625000000):ℚ), ((406799933521/10000000000):ℚ), ((406774670687/10000000000):ℚ), ((203101003799/5000000000):ℚ), ((203088328183/5000000000):ℚ), ((40558787979/1000000000):ℚ), ((81112488171/2000000000):ℚ), ((40495754093/1000000000):ℚ), ((404932014981/10000000000):ℚ), ((404310981989/10000000000):ℚ), ((50535671213/1250000000):ℚ), ((403648194071/10000000000):ℚ), ((403622496123/10000000000):ℚ), ((201484584207/5000000000):ℚ), ((100735846367/2500000000):ℚ), ((40227389639/1000000000):ℚ), ((201124014551/5000000000):ℚ), ((401562369493/10000000000):ℚ), ((200768209257/5000000000):ℚ), ((400834579347/10000000000):ℚ), ((400808545319/10000000000):ℚ), ((400090517699/10000000000):ℚ), ((50008050157/1250000000):ℚ), ((99825994547/2500000000):ℚ)].getD j.val 0
def U (j : Fin 45) : ℝ := (Uq j:ℝ)

def Vq (j : Fin 45) : ℚ := [((412383425953/10000000000):ℚ), ((412947711911/10000000000):ℚ), ((103218683257/2500000000):ℚ), ((82704931499/2000000000):ℚ), ((413451571477/10000000000):ℚ), ((16537090199/400000000):ℚ), ((12938783283/312500000):ℚ), ((414016715547/10000000000):ℚ), ((207321600959/5000000000):ℚ), ((414618822169/10000000000):ℚ), ((207628985607/5000000000):ℚ), ((415233563981/10000000000):ℚ), ((83177072619/2000000000):ℚ), ((3326887449/80000000):ℚ), ((208262684351/5000000000):ℚ), ((104125228683/2500000000):ℚ), ((417177980167/10000000000):ℚ), ((417153506921/10000000000):ℚ), ((208921595301/5000000000):ℚ), ((417818700793/10000000000):ℚ), ((209260497049/5000000000):ℚ), ((104624122607/2500000000):ℚ), ((209605692857/5000000000):ℚ), ((419186870873/10000000000):ℚ), ((419914361479/10000000000):ℚ), ((6560778721/156250000):ℚ), ((52578739797/1250000000):ℚ), ((42060538921/1000000000):ℚ), ((421358054339/10000000000):ℚ), ((84266704399/2000000000):ℚ), ((52762346031/1250000000):ℚ), ((211037117681/5000000000):ℚ), ((422852059917/10000000000):ℚ), ((211413764557/5000000000):ℚ), ((423617930089/10000000000):ℚ), ((423593403977/10000000000):ℚ), ((424396380423/10000000000):ℚ), ((212185930799/5000000000):ℚ), ((425187413493/10000000000):ℚ), ((85032580907/2000000000):ℚ), ((42599103277/1000000000):ℚ), ((85193307249/2000000000):ℚ), ((21340362131/500000000):ℚ), ((426782761077/10000000000):ℚ), ((53451448033/1250000000):ℚ)].getD j.val 0
def V (j : Fin 45) : ℝ := (Vq j:ℝ)

def Kq (j : Fin 45) : ℚ := [((371936847/50000000):ℚ), ((371954261/50000000):ℚ), ((743873089/100000000):ℚ), ((74394221/10000000):ℚ), ((743906687/100000000):ℚ), ((743894867/100000000):ℚ), ((185984779/25000000):ℚ), ((743927267/100000000):ℚ), ((743970347/100000000):ℚ), ((185989617/25000000):ℚ), ((372000173/50000000):ℚ), ((18599711/2500000):ℚ), ((744029081/100000000):ℚ), ((744017149/100000000):ℚ), ((372028261/50000000):ℚ), ((372022281/50000000):ℚ), ((372041317/50000000):ℚ), ((744070649/100000000):ℚ), ((93013423/12500000):ℚ), ((744095373/100000000):ℚ), ((372065369/50000000):ℚ), ((744118703/100000000):ℚ), ((744152661/100000000):ℚ), ((744140603/100000000):ℚ), ((2325541/312500):ℚ), ((744161039/100000000):ℚ), ((372096039/50000000):ℚ), ((372089987/50000000):ℚ), ((1488419/200000):ℚ), ((372098687/50000000):ℚ), ((744225349/100000000):ℚ), ((372106601/50000000):ℚ), ((744239589/100000000):ℚ), ((744227421/100000000):ℚ), ((744252181/100000000):ℚ), ((744239993/100000000):ℚ), ((744263089/100000000):ℚ), ((744250881/100000000):ℚ), ((744272273/100000000):ℚ), ((148852009/20000000):ℚ), ((372139847/50000000):ℚ), ((93033431/12500000):ℚ), ((5814729/781250):ℚ), ((93034131/12500000):ℚ), ((744276807/100000000):ℚ)].getD j.val 0
def K (j : Fin 45) : ℝ := (Kq j:ℝ)

def G : ℝ := ((-2387845619/50000000):ℝ)

theorem g_bound : certificateG (5:ℝ)-2*Real.pi*(5:ℝ)+cellSlope*((1/10000):ℝ) ≤ G := by
  norm_num [G,certificateG,certificateJ,targetNormalizationEntropy,entropyTerm,targetFactorialEndpoints,targetAlpha,targetEndpointTuple,cellSlope,Fin.sum_univ_succ]
  linarith only [log_000.2, log_001.2, log_002.2, log_003.2, log_004.2, log_005.2, log_006.2, log_007.2, log_008.2, log_009.2, log_010.1, log_011.2, log_012.1, log_013.1, log_014.2, log_015.2, log_016.1, log_017.2, log_018.2, log_019.1, log_020.2, log_021.2, log_022.1, log_023.2, log_024.2, log_025.1, log_026.2, log_027.2, log_028.1, log_029.2, log_030.2, log_031.1, log_032.2, log_033.2, log_034.1, log_035.2, log_036.2, log_037.1, log_038.2, log_039.2, log_040.1, log_041.2, log_042.2, log_043.1, log_044.2, log_045.2, atan_000.2, atan_001.1, atan_002.1, atan_003.2, atan_004.1, atan_005.2, atan_006.1, atan_007.2, atan_008.1, atan_009.2, atan_010.1, atan_011.2, atan_012.1, atan_013.2, atan_014.1, atan_015.2, atan_016.1, atan_017.2, atan_018.1, atan_019.2, atan_020.1, atan_021.2, atan_022.1, atan_023.2, pi_machin_enclosure.1]

theorem u_left (j : Fin 45) : ‖(normalizedContourPoint ((49999/10000):ℝ))^2-analyticCenter j‖ ≤ U j := by
  have hc : ∀ j : Fin 45, 0 ≤ Uq j ∧
      (zr ((49999/10000):ℚ)-(centerq j).1)^2+(zi ((49999/10000):ℚ)-(centerq j).2)^2 ≤ (Uq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, U] using (distance_checked ((49999/10000):ℚ) (Uq j) j (hc j).1 (hc j).2)

theorem u_right (j : Fin 45) : ‖(normalizedContourPoint (5:ℝ))^2-analyticCenter j‖ ≤ U j := by
  have hc : ∀ j : Fin 45, 0 ≤ Uq j ∧
      (zr (5:ℚ)-(centerq j).1)^2+(zi (5:ℚ)-(centerq j).2)^2 ≤ (Uq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, U] using (distance_checked (5:ℚ) (Uq j) j (hc j).1 (hc j).2)

theorem v_left (j : Fin 45) : ‖(normalizedContourPoint ((49999/10000):ℝ))^2-star (analyticCenter j)‖ ≤ V j := by
  have hc : ∀ j : Fin 45, 0 ≤ Vq j ∧
      (zr ((49999/10000):ℚ)-(centerq j).1)^2+(zi ((49999/10000):ℚ)+(centerq j).2)^2 ≤ (Vq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, V] using (conjugate_distance_checked ((49999/10000):ℚ) (Vq j) j (hc j).1 (hc j).2)

theorem v_right (j : Fin 45) : ‖(normalizedContourPoint (5:ℝ))^2-star (analyticCenter j)‖ ≤ V j := by
  have hc : ∀ j : Fin 45, 0 ≤ Vq j ∧
      (zr (5:ℚ)-(centerq j).1)^2+(zi (5:ℚ)+(centerq j).2)^2 ≤ (Vq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, V] using (conjugate_distance_checked (5:ℚ) (Vq j) j (hc j).1 (hc j).2)

theorem u_cutoff (j : Fin 45) : (1/50:ℝ) ≤ U j := by
  have hc : ∀ j : Fin 45, (1/50:ℚ) ≤ Uq j := by decide +kernel
  have h := Rat.cast_le (K:=ℝ) |>.mpr (hc j)
  norm_num at h
  exact h

theorem v_cutoff (j : Fin 45) : (1/50:ℝ) ≤ V j := by
  have hc : ∀ j : Fin 45, (1/50:ℚ) ≤ Vq j := by decide +kernel
  have h := Rat.cast_le (K:=ℝ) |>.mpr (hc j)
  norm_num at h
  exact h

theorem log_bound (j : Fin 45) : Real.log (U j+(34/25)*((1/10000):ℝ)^2/4)+Real.log (V j+(34/25)*((1/10000):ℝ)^2/4) ≤ K j := by
  have hc : ∀ j : Fin 45, pairCheck (Uq j+17/5000000000) (Vq j+17/5000000000) (Kq j) = true := by decide +kernel
  have h := pair_checked (Uq j+17/5000000000) (Vq j+17/5000000000) (Kq j) (hc j)
  convert h using 1 <;> norm_num [U,V,K]

theorem knot_bound (m : ℕ) (hm : m ≤ 41) : G+basisKnot m*(∑ j, basisKnotWeight m j*K j) ≤ Numerical.height m := by
  have h := knots_checked ((-2387845619/50000000):ℚ) Kq (by decide +kernel) m hm
  convert h using 1 <;> norm_num [G,K]

theorem cell_width : (5:ℝ)-((49999/10000):ℝ)=(1/10000:ℝ) := by norm_num

def certificate : CellCertificate ((49999/10000):ℝ) (5:ℝ) where
  width_pos := by norm_num
  G := G
  K := K
  U := U
  V := V
  g_bound := by rw [cell_width]; exact g_bound
  u_left := u_left
  u_right := u_right
  v_left := v_left
  v_right := v_right
  u_cutoff := u_cutoff
  v_cutoff := v_cutoff
  log_bound := by rw [cell_width]; exact log_bound
  knot_bound := knot_bound

theorem all_knots_on_cell (m : ℕ) (hm : m ≤ 41) (y : ℝ) (hy : 0 < y) (hyl : ((49999/10000):ℝ) ≤ y) (hy1 : y ≤ (5:ℝ)) :
    certificateG y-2*Real.pi*y+basisKnot m*analyticBasisPotential (basisKnotWeight m) ((normalizedContourPoint y)^2) ≤ Numerical.height m :=
  cell_certificate_sound certificate m hm y hy hyl hy1

#print axioms all_knots_on_cell
end OddZeta.FourValue.Batch.Cell49999
