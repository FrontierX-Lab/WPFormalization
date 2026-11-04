import WPFormalization.Critical.SurvivingMixedIntegration
import WPFormalization.Critical.SurvivingMixedVolumeLintegral
import WPFormalization.Critical.SurvivingMixedVolume
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory Filter
open scoped ENNReal Classical Topology

def survivingMixedWindowTest {r k : ℕ} (I : Fin (r+k) → Set ℝ)
    (x : Fin (r+k) → ℝ) : ℝ≥0∞ := if ∀ i,x i ∈ I i then 1 else 0
lemma survivingMixedWindowTest_measurable {r k : ℕ} (I : Fin (r+k) → Set ℝ)
    (hI : ∀ i,MeasurableSet (I i)) : Measurable (survivingMixedWindowTest I) := by
  apply Measurable.ite (pants_numeric_window_set_measurable _ I hI) measurable_const measurable_const

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  (MI : MirzakhaniIntegration G H T)

include MI in
lemma survivingMixed_window_expectation_eq {g n r k : ℕ}
    (hg : k+2 ≤ g) (hg3 : 3 ≤ g) (hn : 2*r+1 ≤ n)
    (I : Fin (r+k) → Set ℝ) (hI : ∀ i,MeasurableSet (I i))
    (L : ℝ) (hL : 0 ≤ L) (hIL : ∀ i,I i ⊆ Set.Icc 0 L) :
    (∫⁻ X, survivingMixedOrbitSum T (g:=g) (n:=n) (r:=r) (k:=k)
      (survivingMixedWindowTest I) X ∂wpProbability G g n) =
        ENNReal.ofReal (survivingMixedCutContribution P g n r k I) := by
  rw [survivingMixed_probability_lintegral T MI hg hg3 (by omega) _
    (survivingMixedWindowTest_measurable I hI)]
  have hi : survivingMixedCutIntegral P g n r k (survivingMixedWindowTest I)=
      ENNReal.ofReal (survivingMixedVolumeIntegral P g n r k I) :=
    surviving_mixed_window_lintegral_eq P G g n r k (by omega) hn I hI L hL hIL
  rw [hi]
  have hs : Stable g n := by unfold Stable; omega
  have hV : 0 < volumeModel P g n := cut_volumeModel_pos P g n (by omega) hs
  have hv := Geometry.cuspVolume_eq_volumeModel P G g n hs
  unfold cuspVolume wpVolume at hv
  have hm : G.wpMeasure g n (fun _ => 0) Set.univ=ENNReal.ofReal (volumeModel P g n) := by
    rw [←hv]
    exact (ENNReal.ofReal_toReal (G.finite_volume g n _ hs (by simp))).symm
  rw [hm]
  have he : survivingMixedCutContribution P g n r k I=
      (volumeModel P g n)⁻¹*((n.descFactorial (2*r):ℝ)/(2:ℝ)^(r+k))*
        survivingMixedVolumeIntegral P g n r k I := by
    unfold survivingMixedCutContribution
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hV.le)
      (div_nonneg (Nat.cast_nonneg _) (by positivity))),
    ENNReal.ofReal_mul (inv_nonneg.mpr hV.le),ENNReal.ofReal_inv_of_pos hV,
    ENNReal.ofReal_div_of_pos (by positivity : 0 < (2:ℝ)^(r+k))]
  simp

include MI in
lemma survivingMixed_window_expectation_tendsto (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) (r k : ℕ)
    (I : Fin (r+k) → Set ℝ) (hI : ∀ i,MeasurableSet (I i))
    (L : ℝ) (hL : 0 ≤ L) (hIL : ∀ i,I i ⊆ Set.Icc 0 L) :
    Tendsto (fun g => ∫⁻ X, survivingMixedOrbitSum T (g:=g) (n:=n g) (r:=r) (k:=k)
      (survivingMixedWindowTest I) X ∂wpProbability G g (n g)) atTop
      (𝓝 (ENNReal.ofReal ((∏ j : Fin r, ∫ s in I (Fin.castAdd k j),criticalIntensityDensity c s)*
        ∏ i : Fin k, ∫ t in I (Fin.natAdd r i),tightIntensityDensity t))) := by
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (surviving_mixed_cut_contribution_tendsto P n c hc hn r k I hI L hL hIL)
  apply ht.congr'
  have hntop := surviving_critical_cusps_tendsto n c hc hn
  filter_upwards [hntop.eventually_ge_atTop (2*r+1),eventually_ge_atTop (max (k+2) 3)] with g hng hg
  exact (survivingMixed_window_expectation_eq T MI (by omega) (by omega) hng I hI L hL hIL).symm
end WP.Critical
