import FourValueBatchEnclosures5669

noncomputable section
namespace OddZeta.FourValue.Batch.Cell5669
open OddZeta.FourValue.Transcendental
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true

def Uq (j : Fin 45) : ℚ := [((15834970501/10000000000):ℚ), ((15265428803/10000000000):ℚ), ((3069942011/2000000000):ℚ), ((14684929733/10000000000):ℚ), ((14766673407/10000000000):ℚ), ((739758639/500000000):ℚ), ((1417252653/1000000000):ℚ), ((7100123279/5000000000):ℚ), ((1695887157/1250000000):ℚ), ((13594050979/10000000000):ℚ), ((12950218981/10000000000):ℚ), ((3244104901/2500000000):ℚ), ((12321730493/10000000000):ℚ), ((6173595719/5000000000):ℚ), ((5840737903/5000000000):ℚ), ((11706210791/10000000000):ℚ), ((11029303997/10000000000):ℚ), ((5526663567/5000000000):ℚ), ((2073013809/2000000000):ℚ), ((5194197493/5000000000):ℚ), ((9688629673/10000000000):ℚ), ((971127381/1000000000):ℚ), ((2249962299/2500000000):ℚ), ((4510913977/5000000000):ℚ), ((2074648843/2500000000):ℚ), ((2079981659/2500000000):ℚ), ((1516948051/2000000000):ℚ), ((304217761/400000000):ℚ), ((6858160053/10000000000):ℚ), ((3439129737/5000000000):ℚ), ((611873499/1000000000):ℚ), ((767282257/1250000000):ℚ), ((5366349171/10000000000):ℚ), ((5385331699/10000000000):ℚ), ((4600890453/10000000000):ℚ), ((4619381673/10000000000):ℚ), ((3822250317/10000000000):ℚ), ((3840324409/10000000000):ℚ), ((94697617/312500000):ℚ), ((609621393/2000000000):ℚ), ((1112504549/5000000000):ℚ), ((448551427/2000000000):ℚ), ((140620801/1000000000):ℚ), ((1424610489/10000000000):ℚ), ((37279011/625000000):ℚ)].getD j.val 0
def U (j : Fin 45) : ℝ := (Uq j:ℝ)

def Vq (j : Fin 45) : ℚ := [((15834970501/10000000000):ℚ), ((2030567149/1250000000):ℚ), ((1632376399/1000000000):ℚ), ((16681198321/10000000000):ℚ), ((837660223/500000000):ℚ), ((8389164943/5000000000):ℚ), ((2151130301/1250000000):ℚ), ((17231878443/10000000000):ℚ), ((8845112331/5000000000):ℚ), ((8855452313/5000000000):ℚ), ((18195748203/10000000000):ℚ), ((4553601231/2500000000):ℚ), ((117029169/62500000):ℚ), ((4685357843/2500000000):ℚ), ((9638048233/5000000000):ℚ), ((4822774027/2500000000):ℚ), ((19849215129/10000000000):ℚ), ((19862573733/10000000000):ℚ), ((2555408173/1250000000):ℚ), ((20455101897/10000000000):ℚ), ((10528776151/5000000000):ℚ), ((5266995129/2500000000):ℚ), ((10845720843/5000000000):ℚ), ((10850284979/5000000000):ℚ), ((4468871477/2000000000):ℚ), ((1397018031/625000000):ℚ), ((23015778143/10000000000):ℚ), ((2302260927/1000000000):ℚ), ((23705234173/10000000000):ℚ), ((23711056941/10000000000):ℚ), ((24412303597/10000000000):ℚ), ((24417204201/10000000000):ℚ), ((12568304437/5000000000):ℚ), ((6285167061/2500000000):ℚ), ((3234726661/1250000000):ℚ), ((25881107291/10000000000):ℚ), ((13317808777/5000000000):ℚ), ((13319108609/5000000000):ℚ), ((1713109787/625000000):ℚ), ((27411728339/10000000000):ℚ), ((28199996481/10000000000):ℚ), ((28201402369/10000000000):ℚ), ((7251532901/2500000000):ℚ), ((14503514787/5000000000):ℚ), ((14914213061/5000000000):ℚ)].getD j.val 0
def V (j : Fin 45) : ℝ := (Vq j:ℝ)

def Kq (j : Fin 45) : ℚ := [((45963573/50000000):ℚ), ((45408861/50000000):ℚ), ((91854837/100000000):ℚ), ((11199173/12500000):ℚ), ((45289611/50000000):ℚ), ((18184379/20000000):ℚ), ((89157013/100000000):ℚ), ((44742511/50000000):ℚ), ((87548957/100000000):ℚ), ((43932131/50000000):ℚ), ((85713047/100000000):ℚ), ((43008821/50000000):ℚ), ((41801799/50000000):ℚ), ((8389951/10000000):ℚ), ((16233999/20000000):ℚ), ((81459301/100000000):ℚ), ((39177501/50000000):ℚ), ((15727971/20000000):ℚ), ((37546237/50000000):ℚ), ((75375147/100000000):ℚ), ((7130421/10000000):ℚ), ((35793583/50000000):ℚ), ((8361943/12500000):ℚ), ((16795383/25000000):ℚ), ((241207/390625):ℚ), ((62041197/100000000):ℚ), ((27857409/50000000):ℚ), ((875267/1562500):ℚ), ((48596489/100000000):ℚ), ((24456847/50000000):ℚ), ((8025449/20000000):ℚ), ((1011647/2500000):ℚ), ((5986059/20000000):ℚ), ((946861/3125000):ℚ), ((8723283/50000000):ℚ), ((8930197/50000000):ℚ), ((1791849/100000000):ℚ), ((28417/1250000):ℚ), ((-2320021/12500000):ℚ), ((-17967847/100000000):ℚ), ((-46608731/100000000):ℚ), ((-45809249/100000000):ℚ), ((-89676619/100000000):ℚ), ((-11046669/12500000):ℚ), ((-86322219/50000000):ℚ)].getD j.val 0
def K (j : Fin 45) : ℝ := (Kq j:ℝ)

def G : ℝ := ((-469941093/50000000):ℝ)

theorem g_bound : certificateG ((567/1000):ℝ)-2*Real.pi*((567/1000):ℝ)+cellSlope*((1/10000):ℝ) ≤ G := by
  norm_num [G,certificateG,certificateJ,targetNormalizationEntropy,entropyTerm,targetFactorialEndpoints,targetAlpha,targetEndpointTuple,cellSlope,Fin.sum_univ_succ]
  linarith only [log_000.2, log_001.2, log_002.2, log_003.2, log_004.2, log_005.2, log_006.2, log_007.2, log_008.2, log_009.2, log_010.1, log_011.2, log_012.1, log_013.1, log_014.2, log_015.2, log_016.1, log_017.2, log_018.2, log_019.1, log_020.2, log_021.2, log_022.1, log_023.2, log_024.2, log_025.1, log_026.2, log_027.2, log_028.1, log_029.2, log_030.2, log_031.1, log_032.2, log_033.2, log_034.1, log_035.2, log_036.2, log_037.1, log_038.2, log_039.2, log_040.1, log_041.2, log_042.2, log_043.1, log_044.2, log_045.2, atan_000.2, atan_001.1, atan_002.1, atan_003.2, atan_004.1, atan_005.2, atan_006.1, atan_007.2, atan_008.1, atan_009.2, atan_010.1, atan_011.2, atan_012.1, atan_013.2, atan_014.1, atan_015.2, atan_016.1, atan_017.2, atan_018.1, atan_019.2, atan_020.1, atan_021.2, atan_022.1, atan_023.2, pi_machin_enclosure.1]

theorem u_left (j : Fin 45) : ‖(normalizedContourPoint ((5669/10000):ℝ))^2-analyticCenter j‖ ≤ U j := by
  have hc : ∀ j : Fin 45, 0 ≤ Uq j ∧
      (zr ((5669/10000):ℚ)-(centerq j).1)^2+(zi ((5669/10000):ℚ)-(centerq j).2)^2 ≤ (Uq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, U] using (distance_checked ((5669/10000):ℚ) (Uq j) j (hc j).1 (hc j).2)

theorem u_right (j : Fin 45) : ‖(normalizedContourPoint ((567/1000):ℝ))^2-analyticCenter j‖ ≤ U j := by
  have hc : ∀ j : Fin 45, 0 ≤ Uq j ∧
      (zr ((567/1000):ℚ)-(centerq j).1)^2+(zi ((567/1000):ℚ)-(centerq j).2)^2 ≤ (Uq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, U] using (distance_checked ((567/1000):ℚ) (Uq j) j (hc j).1 (hc j).2)

theorem v_left (j : Fin 45) : ‖(normalizedContourPoint ((5669/10000):ℝ))^2-star (analyticCenter j)‖ ≤ V j := by
  have hc : ∀ j : Fin 45, 0 ≤ Vq j ∧
      (zr ((5669/10000):ℚ)-(centerq j).1)^2+(zi ((5669/10000):ℚ)+(centerq j).2)^2 ≤ (Vq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, V] using (conjugate_distance_checked ((5669/10000):ℚ) (Vq j) j (hc j).1 (hc j).2)

theorem v_right (j : Fin 45) : ‖(normalizedContourPoint ((567/1000):ℝ))^2-star (analyticCenter j)‖ ≤ V j := by
  have hc : ∀ j : Fin 45, 0 ≤ Vq j ∧
      (zr ((567/1000):ℚ)-(centerq j).1)^2+(zi ((567/1000):ℚ)+(centerq j).2)^2 ≤ (Vq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, V] using (conjugate_distance_checked ((567/1000):ℚ) (Vq j) j (hc j).1 (hc j).2)

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
  have h := knots_checked ((-469941093/50000000):ℚ) Kq (by decide +kernel) m hm
  convert h using 1 <;> norm_num [G,K]

theorem cell_width : ((567/1000):ℝ)-((5669/10000):ℝ)=(1/10000:ℝ) := by norm_num

def certificate : CellCertificate ((5669/10000):ℝ) ((567/1000):ℝ) where
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

theorem all_knots_on_cell (m : ℕ) (hm : m ≤ 41) (y : ℝ) (hy : 0 < y) (hyl : ((5669/10000):ℝ) ≤ y) (hy1 : y ≤ ((567/1000):ℝ)) :
    certificateG y-2*Real.pi*y+basisKnot m*analyticBasisPotential (basisKnotWeight m) ((normalizedContourPoint y)^2) ≤ Numerical.height m :=
  cell_certificate_sound certificate m hm y hy hyl hy1

#print axioms all_knots_on_cell
end OddZeta.FourValue.Batch.Cell5669
