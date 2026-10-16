import FourValueBatchEnclosures

noncomputable section
namespace OddZeta.FourValue.Batch.Cell0
open OddZeta.FourValue.Transcendental
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true

def Uq (j : Fin 45) : ℚ := [((3/100):ℚ), ((782797707/10000000000):ℚ), ((587513617/10000000000):ℚ), ((169666769/1250000000):ℚ), ((1184042229/10000000000):ℚ), ((1138049209/10000000000):ℚ), ((1789846991/10000000000):ℚ), ((1743775287/10000000000):ℚ), ((96207243/400000000):ℚ), ((73737393/312500000):ℚ), ((3030289797/10000000000):ℚ), ((2985407217/10000000000):ℚ), ((733082151/2000000000):ℚ), ((724266139/2000000000):ℚ), ((2155386987/5000000000):ℚ), ((4267548741/10000000000):ℚ), ((2483301029/5000000000):ℚ), ((984851989/2000000000):ℚ), ((2816555177/5000000000):ℚ), ((2795833161/5000000000):ℚ), ((788813389/1250000000):ℚ), ((3134984051/5000000000):ℚ), ((349949683/500000000):ℚ), ((6959361483/10000000000):ℚ), ((7698764577/10000000000):ℚ), ((3830018799/5000000000):ℚ), ((8410007863/10000000000):ℚ), ((8372182049/10000000000):ℚ), ((2283226281/2500000000):ℚ), ((1819194943/2000000000):ℚ), ((1973526349/2000000000):ℚ), ((614474357/625000000):ℚ), ((1061435707/1000000000):ℚ), ((10579195433/10000000000):ℚ), ((11373244579/10000000000):ℚ), ((11338954637/10000000000):ℚ), ((12144452067/10000000000):ℚ), ((2422204913/2000000000):ℚ), ((1616016477/1250000000):ℚ), ((515822283/400000000):ℚ), ((3431107693/2500000000):ℚ), ((2738539757/2000000000):ℚ), ((1816686339/1250000000):ℚ), ((7251295613/5000000000):ℚ), ((15325370991/10000000000):ℚ)].getD j.val 0
def U (j : Fin 45) : ℝ := (Uq j:ℝ)

def Vq (j : Fin 45) : ℚ := [((3/100):ℚ), ((783184199/10000000000):ℚ), ((588640341/10000000000):ℚ), ((1358072237/10000000000):ℚ), ((1185192037/10000000000):ℚ), ((569675379/5000000000):ℚ), ((1791020541/10000000000):ℚ), ((872524293/5000000000):ℚ), ((150398633/625000000):ℚ), ((236086757/1000000000):ℚ), ((151575497/500000000):ℚ), ((2986685873/10000000000):ℚ), ((3666653521/10000000000):ℚ), ((1811310853/5000000000):ℚ), ((1078009719/2500000000):ℚ), ((26680341/62500000):ℚ), ((993577721/2000000000):ℚ), ((4925581913/10000000000):ℚ), ((704302257/1250000000):ℚ), ((349562823/625000000):ℚ), ((6311835483/10000000000):ℚ), ((3135662097/5000000000):ℚ), ((350017111/500000000):ℚ), ((87009187/125000000):ℚ), ((1925033213/2500000000):ℚ), ((1915357113/2500000000):ℚ), ((2102848847/2500000000):ℚ), ((2093397543/2500000000):ℚ), ((4567155721/5000000000):ℚ), ((9097399931/10000000000):ℚ), ((9869056407/10000000000):ℚ), ((9833031799/10000000000):ℚ), ((2653949909/2500000000):ℚ), ((5290327067/5000000000):ℚ), ((11374704619/10000000000):ℚ), ((1417553709/1250000000):ℚ), ((6072964579/5000000000):ℚ), ((12112515639/10000000000):ℚ), ((12929625547/10000000000):ℚ), ((6448531941/5000000000):ℚ), ((6862970369/5000000000):ℚ), ((3423555253/2500000000):ℚ), ((14535016519/10000000000):ℚ), ((14504128557/10000000000):ℚ), ((3831730777/2500000000):ℚ)].getD j.val 0
def V (j : Fin 45) : ℝ := (Vq j:ℝ)

def Kq (j : Fin 45) : ℚ := [((-175327889/25000000):ℚ), ((-509443843/100000000):ℚ), ((-566696583/100000000):ℚ), ((-99839533/25000000):ℚ), ((-42663311/10000000):ℚ), ((-108634899/25000000):ℚ), ((-344025441/100000000):ℚ), ((-43654191/12500000):ℚ), ((-14247111/5000000):ℚ), ((-36095629/12500000):ℚ), ((-59686277/25000000):ℚ), ((-241726963/100000000):ℚ), ((-50173759/25000000):ℚ), ((-101556531/50000000):ℚ), ((-33652837/20000000):ℚ), ((-170278503/100000000):ℚ), ((-139943933/100000000):ℚ), ((-1133243/800000):ℚ), ((-22952291/20000000):ℚ), ((-11623761/10000000):ℚ), ((-92052761/100000000):ℚ), ((-46670569/50000000):ℚ), ((-17836119/25000000):ℚ), ((-36239869/50000000):ℚ), ((-6535909/12500000):ℚ), ((-53295483/100000000):ℚ), ((-17308019/50000000):ℚ), ((-3551729/10000000):ℚ), ((-4531213/25000000):ℚ), ((-3786991/20000000):ℚ), ((-530121/20000000):ℚ), ((-1691111/50000000):ℚ), ((11938077/100000000):ℚ), ((2254929/20000000):ℚ), ((5149709/20000000):ℚ), ((6286203/25000000):ℚ), ((19434817/50000000):ℚ), ((1532741/4000000):ℚ), ((2055027/4000000):ℚ), ((25435617/50000000):ℚ), ((31664743/50000000):ℚ), ((1257333/2000000):ℚ), ((37392309/50000000):ℚ), ((1487181/2000000):ℚ), ((10674381/12500000):ℚ)].getD j.val 0
def K (j : Fin 45) : ℝ := (Kq j:ℝ)

def G : ℝ := ((-19410431/4000000):ℝ)

theorem g_bound : certificateG ((1/10000):ℝ)-2*Real.pi*((1/10000):ℝ)+cellSlope*((1/10000):ℝ) ≤ G := by
  norm_num [G,certificateG,certificateJ,targetNormalizationEntropy,entropyTerm,targetFactorialEndpoints,targetAlpha,targetEndpointTuple,cellSlope,Fin.sum_univ_succ]
  linarith only [log_000.2, log_001.2, log_002.2, log_003.2, log_004.2, log_005.2, log_006.2, log_007.2, log_008.2, log_009.2, log_010.1, log_011.2, log_012.1, log_013.1, log_014.2, log_015.2, log_016.1, log_017.2, log_018.2, log_019.1, log_020.2, log_021.2, log_022.1, log_023.2, log_024.2, log_025.1, log_026.2, log_027.2, log_028.1, log_029.2, log_030.2, log_031.1, log_032.2, log_033.2, log_034.1, log_035.2, log_036.2, log_037.1, log_038.2, log_039.2, log_040.1, log_041.2, log_042.2, log_043.1, log_044.2, log_045.2, atan_000.2, atan_001.1, atan_002.1, atan_003.2, atan_004.1, atan_005.2, atan_006.1, atan_007.2, atan_008.1, atan_009.2, atan_010.1, atan_011.2, atan_012.1, atan_013.2, atan_014.1, atan_015.2, atan_016.1, atan_017.2, atan_018.1, atan_019.2, atan_020.1, atan_021.2, atan_022.1, atan_023.2, pi_machin_enclosure.2]

theorem u_left (j : Fin 45) : ‖(normalizedContourPoint (0:ℝ))^2-analyticCenter j‖ ≤ U j := by
  have hc : ∀ j : Fin 45, 0 ≤ Uq j ∧
      (zr (0:ℚ)-(centerq j).1)^2+(zi (0:ℚ)-(centerq j).2)^2 ≤ (Uq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, U] using (distance_checked (0:ℚ) (Uq j) j (hc j).1 (hc j).2)

theorem u_right (j : Fin 45) : ‖(normalizedContourPoint ((1/10000):ℝ))^2-analyticCenter j‖ ≤ U j := by
  have hc : ∀ j : Fin 45, 0 ≤ Uq j ∧
      (zr ((1/10000):ℚ)-(centerq j).1)^2+(zi ((1/10000):ℚ)-(centerq j).2)^2 ≤ (Uq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, U] using (distance_checked ((1/10000):ℚ) (Uq j) j (hc j).1 (hc j).2)

theorem v_left (j : Fin 45) : ‖(normalizedContourPoint (0:ℝ))^2-star (analyticCenter j)‖ ≤ V j := by
  have hc : ∀ j : Fin 45, 0 ≤ Vq j ∧
      (zr (0:ℚ)-(centerq j).1)^2+(zi (0:ℚ)+(centerq j).2)^2 ≤ (Vq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, V] using (conjugate_distance_checked (0:ℚ) (Vq j) j (hc j).1 (hc j).2)

theorem v_right (j : Fin 45) : ‖(normalizedContourPoint ((1/10000):ℝ))^2-star (analyticCenter j)‖ ≤ V j := by
  have hc : ∀ j : Fin 45, 0 ≤ Vq j ∧
      (zr ((1/10000):ℚ)-(centerq j).1)^2+(zi ((1/10000):ℚ)+(centerq j).2)^2 ≤ (Vq j)^2 := by decide +kernel
  simpa only [Rat.cast_zero, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, V] using (conjugate_distance_checked ((1/10000):ℚ) (Vq j) j (hc j).1 (hc j).2)

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
  have h := knots_checked ((-19410431/4000000):ℚ) Kq (by decide +kernel) m hm
  convert h using 1 <;> norm_num [G,K]

def certificate : CellCertificate (0:ℝ) ((1/10000):ℝ) where
  width_pos := by norm_num
  G := G
  K := K
  U := U
  V := V
  g_bound := by simpa using g_bound
  u_left := u_left
  u_right := u_right
  v_left := v_left
  v_right := v_right
  u_cutoff := u_cutoff
  v_cutoff := v_cutoff
  log_bound := by simpa using log_bound
  knot_bound := knot_bound

theorem all_knots_on_first_cell (m : ℕ) (hm : m ≤ 41) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ ((1/10000):ℝ)) :
    certificateG y-2*Real.pi*y+basisKnot m*analyticBasisPotential (basisKnotWeight m) ((normalizedContourPoint y)^2) ≤ Numerical.height m :=
  cell_certificate_sound certificate m hm y hy hy.le hy1

#print axioms all_knots_on_first_cell
end OddZeta.FourValue.Batch.Cell0
