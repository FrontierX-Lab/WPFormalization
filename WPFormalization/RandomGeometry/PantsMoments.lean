import WPFormalization.RandomGeometry.PantsMomentIntegration
import WPFormalization.RandomGeometry.PantsBoxLintegral
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsCutMoments

/-! True geometric first and second factorial moments; the actual WP count is
integrated, then the proved orbit partition and classical integration are used. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T) {g n r : ℕ}

include C MI in
lemma pants_factorial_moment_eq_cut_integral (hg : 2 ≤ g) (hr : 0 < r) (hn : 2*r ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1) :
    (∫X : G.Moduli g n (fun _ => 0), ((H.pantsCount X L).descFactorial r : ℝ)
      ∂wpProbability G g n) =
      ((Fintype.card (PantsStarOrbit T g n r) : ℝ)/volumeModel P g n)*
        weightedBoxIntegral P g (n-r) r (show r ≤ n-r by omega) L := by
  have hm : Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      ((H.pantsCount X L).descFactorial r : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k.descFactorial r : ℝ))).comp
      (H.measurable_pantsCount L)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
    (fun X => Nat.cast_nonneg ((H.pantsCount X L).descFactorial r))) hm.aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast]
  rw [pants_factorial_probability_lintegral T C MI hg hr hn L hL]
  have hbox := pantsBox_lintegral_eq P G g (n-r) r (show r ≤ n-r by omega)
    (by unfold Stable; omega) L
  change pantsOrthantCutIntegral P g n r hn L = _ at hbox
  rw [hbox]
  have hw : 0 ≤ weightedBoxIntegral P g (n-r) r (show r ≤ n-r by omega) L :=
    integral_nonneg_of_ae (pants_box_integrand_nonneg P G g (n-r) r
      (show r ≤ n-r by omega) (by unfold Stable; omega) L)
  have hmass : (G.wpMeasure g n (fun _ => 0) Set.univ).toReal = volumeModel P g n :=
    WP.Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable; omega)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hw,hmass]
  ring

lemma pantsStarOrbit_card_real (g n r : ℕ) (hg : 2 ≤ g) :
    (Fintype.card (PantsStarOrbit T g n r) : ℝ) =
      (n.descFactorial (2*r) : ℝ)/(2:ℝ)^r := by
  apply (eq_div_iff (pow_ne_zero r (by norm_num : (2:ℝ) ≠ 0))).2
  exact_mod_cast pantsStarOrbit_card T g n r hg

include C MI in
lemma pants_factorial_moment_formula (hg : 2 ≤ g) (hr : 0 < r) (hn : 2*r ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1) :
    (∫X : G.Moduli g n (fun _ => 0), ((H.pantsCount X L).descFactorial r : ℝ)
      ∂wpProbability G g n) =
      ((n.descFactorial (2*r) : ℝ)/((2:ℝ)^r*volumeModel P g n))*
        weightedBoxIntegral P g (n-r) r (show r ≤ n-r by omega) L := by
  rw [pants_factorial_moment_eq_cut_integral G H T C MI hg hr hn L hL,
    pantsStarOrbit_card_real G H T g n r hg]
  ring

include C MI in
lemma pants_first_moment_eq_cut (hg : 2 ≤ g) (hn : 2 ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1) :
    (∫X : G.Moduli g n (fun _ => 0), (H.pantsCount X L : ℝ) ∂wpProbability G g n) =
      pantsFirstCutIntegral P g n L := by
  have h := pants_factorial_moment_formula G H T C MI (r:=1) hg (by omega) (by omega) L hL
  simp only [Nat.descFactorial_one] at h
  rw [pantsFirstCutIntegral,dif_pos hn]
  convert h using 1
  simp only [Nat.mul_one,Nat.cast_mul,Nat.descFactorial_succ,Nat.descFactorial_zero,
    Nat.mul_one,Nat.sub_zero,Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_one,pow_one]
  ring

lemma cast_descFactorial_two (N : ℕ) :
    (N.descFactorial 2 : ℝ)=(N:ℝ)*((N:ℝ)-1) := by
  cases N with
  | zero => norm_num
  | succ N => simp [Nat.descFactorial_succ]; ring

include C MI in
lemma pants_second_factorial_moment_eq_cut (hg : 2 ≤ g) (hn : 4 ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1) :
    (∫X : G.Moduli g n (fun _ => 0),
      (H.pantsCount X L : ℝ)*((H.pantsCount X L : ℝ)-1) ∂wpProbability G g n) =
      pantsSecondCutIntegral P g n L := by
  have h := pants_factorial_moment_formula G H T C MI (r:=2) hg (by omega) (by omega) L hL
  simp only [cast_descFactorial_two] at h
  rw [pantsSecondCutIntegral,dif_pos hn]
  convert h using 1
  norm_num only [Nat.reduceMul,show (4:ℕ)=3+1 by rfl,Nat.descFactorial_succ,
    Nat.descFactorial_zero,Nat.mul_one,Nat.sub_zero,Nat.cast_mul,
    Nat.cast_sub (show 3 ≤ n by omega),Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_one,Nat.cast_ofNat,pow_two]
  ring

end WP.RandomGeometry
