import WPFormalization.Critical.SurvivingMixedRootVolume
import WPFormalization.Critical.SurvivingMixedOrbit
import WPFormalization.RandomGeometry.PantsMomentIntegration
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory
open scoped ENNReal

/-- The exact standard-root integral for the surviving actual mixed cuts. -/
def survivingMixedCutIntegral (P : PsiTheory) (g n r k : ℕ)
    (F : (Fin (r+k) → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x : Fin (r+k) → ℝ in {x | ∀ i, 0 ≤ x i},
    F x * ENNReal.ofReal (boundaryVolumeModel P (g-k) (n-r+2*k)
      (survivingBoundaryLengths r k n x)) * ∏ i, ENNReal.ofReal (x i)

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  (MI : MirzakhaniIntegration G H T) {g n r k : ℕ}

lemma survivingMixedOrbit_volumeProduct (hg : k+2 ≤ g) (hn : 2*r ≤ n)
    (o : SurvivingMixedOrbit T g n r k) (x : Fin (r+k) → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (T.cut o.val).volumeProduct G x =
      boundaryVolumeModel P (g-k) (n-r+2*k) (survivingBoundaryLengths r k n x) := by
  exact ((survivingMixedOrbitIso T o).volumeProduct_eq G x hx
    (survivingMixed_stable g n r k _ hg)).symm.trans
      (survivingMixed_volumeProduct P G g n r k (survivingMixedOrbitLabel T o) hg hn x hx)

include MI in
lemma survivingMixedOrbit_lintegral (hg : k+2 ≤ g) (hg3 : 3 ≤ g) (hn : 2*r ≤ n)
    (o : SurvivingMixedOrbit T g n r k) (F : (Fin (r+k) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ X, T.orbitSum o.val F X ∂G.wpMeasure g n (fun _ => 0)) =
      ((2:ℝ≥0∞)^k)⁻¹ * survivingMixedCutIntegral P g n r k F := by
  rw [MI.orbit_integral o.val (by unfold Stable; omega)
    (by intro h; have := congrArg Prod.fst h; simp at this; omega)
    (by intro h; have := congrArg Prod.fst h; simp at this; omega)
    F hF,survivingMixedOrbit_coefficient T hg]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (pants_orthant_measurable (r+k))] with x hx
  rw [survivingMixedOrbit_volumeProduct T hg hn o x hx]

/-- The physical ordered mixed-star count, summed over every original cusp
pair label, has no abstract moment or expected-count premise. -/
def survivingMixedOrbitSum (F : (Fin (r+k) → ℝ) → ℝ≥0∞)
    (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑ o : SurvivingMixedOrbit T g n r k, T.orbitSum o.val F X

include MI in
lemma survivingMixedOrbitSum_measurable (F : (Fin (r+k) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (survivingMixedOrbitSum T (g:=g) (n:=n) (r:=r) (k:=k) F) := by
  apply Finset.measurable_sum
  intro o ho
  exact MI.orbitSum_measurable o.val F hF

lemma survivingMixedOrbit_prefactor (hg : k+2 ≤ g) :
    (Fintype.card (SurvivingMixedOrbit T g n r k) : ℝ≥0∞)*((2:ℝ≥0∞)^k)⁻¹ =
      (n.descFactorial (2*r) : ℝ≥0∞)/(2:ℝ≥0∞)^(r+k) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_div]
  have hc : (Fintype.card (SurvivingMixedOrbit T g n r k) : ℝ)*2^r=
      (n.descFactorial (2*r) : ℝ) := by exact_mod_cast survivingMixedOrbit_card T g n r k hg
  rw [←hc,pow_add]
  field_simp

include MI in
lemma survivingMixed_wp_lintegral (hg : k+2 ≤ g) (hg3 : 3 ≤ g) (hn : 2*r ≤ n)
    (F : (Fin (r+k) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ X, survivingMixedOrbitSum T (g:=g) (n:=n) (r:=r) (k:=k) F X
      ∂G.wpMeasure g n (fun _ => 0)) =
    ((n.descFactorial (2*r):ℝ≥0∞)/(2:ℝ≥0∞)^(r+k))*survivingMixedCutIntegral P g n r k F := by
  unfold survivingMixedOrbitSum
  rw [lintegral_finsetSum _ (fun o ho => MI.orbitSum_measurable o.val F hF)]
  simp_rw [survivingMixedOrbit_lintegral T MI hg hg3 hn _ F hF]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,survivingMixedOrbit_prefactor T hg]

include MI in
lemma survivingMixed_probability_lintegral (hg : k+2 ≤ g) (hg3 : 3 ≤ g) (hn : 2*r ≤ n)
    (F : (Fin (r+k) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ X, survivingMixedOrbitSum T (g:=g) (n:=n) (r:=r) (k:=k) F X
      ∂wpProbability G g n) =
    (G.wpMeasure g n (fun _ => 0) Set.univ)⁻¹ *
      ((n.descFactorial (2*r):ℝ≥0∞)/(2:ℝ≥0∞)^(r+k))*survivingMixedCutIntegral P g n r k F := by
  rw [wpProbability,lintegral_smul_measure,survivingMixed_wp_lintegral T MI hg hg3 hn F hF]
  simp only [smul_eq_mul,mul_assoc]
end WP.Critical
