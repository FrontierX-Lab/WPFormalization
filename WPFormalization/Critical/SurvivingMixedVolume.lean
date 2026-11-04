import WPFormalization.Critical.SurvivingMixedVolumeIntegrals
import WPFormalization.Critical.SurvivingMixedVolumePrefactor
import WPFormalization.Statements.Intensities

/-! The exact actual volume contribution (G.6) converges to the product of
pants and nonseparating-loop intensity integrals on bounded Borel windows.
No orbit, factorial moment, or joint Poisson conclusion is assumed here. -/
noncomputable section
namespace WP.Critical
open Filter Set MeasureTheory
open scoped Topology

lemma surviving_pants_intensity_eq_boundaryFactor (c s : ℝ) :
    criticalIntensityDensity c s = c^2/(16*Real.pi^2)*(s*boundaryFactor 0 s) := by
  rw [(boundary_factor_endpoints s).1]
  by_cases hs : s=0
  · simp [hs,criticalIntensityDensity]
  · rw [if_neg hs]
    unfold criticalIntensityDensity
    field_simp
    ring

lemma surviving_loop_intensity_eq_boundaryFactor (t : ℝ) :
    tightIntensityDensity t = (1/2:ℝ)*(t*boundaryFactor 0 t^2) := by
  rw [(boundary_factor_endpoints t).1]
  by_cases ht : t=0
  · simp [ht,tightIntensityDensity]
  · rw [if_neg ht]
    have hc := Real.cosh_two_mul (t/2)
    have hs := Real.cosh_sq_sub_sinh_sq (t/2)
    rw [show 2*(t/2)=t by ring] at hc
    unfold tightIntensityDensity
    field_simp
    nlinarith

lemma surviving_mixed_limit_integral_product (r k : ℕ) (I : Fin (r+k) → Set ℝ) :
    (∫ x : Fin (r+k) → ℝ in {x | ∀ i,x i ∈ I i}, survivingMixedLimitIntegrand r k x) =
      (∏ j : Fin r, ∫ s in I (Fin.castAdd k j),s*boundaryFactor 0 s) *
      ∏ i : Fin k, ∫ t in I (Fin.natAdd r i),t*boundaryFactor 0 t^2 := by
  let f : Fin (r+k) → ℝ → ℝ := Fin.append
    (fun _ : Fin r => fun s => s*boundaryFactor 0 s)
    (fun _ : Fin k => fun t => t*boundaryFactor 0 t^2)
  have hprod : (survivingMixedLimitIntegrand r k) =
      fun x : Fin (r+k) → ℝ => ∏ i,f i (x i) := by
    funext x
    simp only [survivingMixedLimitIntegrand,survivingBoundaryFactor,
      Fin.prod_univ_add,Fin.append_left,Fin.append_right,f,Finset.prod_mul_distrib]
    ring
  have hW : {x : Fin (r+k) → ℝ | ∀ i,x i ∈ I i}=Set.univ.pi I := by ext x;simp
  rw [hprod,hW,volume_pi,Measure.restrict_pi_pi,integral_fintype_prod_eq_prod f,Fin.prod_univ_add]
  simp only [f,Fin.append_left,Fin.append_right]

lemma surviving_mixed_intensity_integral_product (c : ℝ) (r k : ℕ)
    (I : Fin (r+k) → Set ℝ) :
    ((c^2/(16*Real.pi^2))^r*(1/2:ℝ)^k) *
      (∫ x : Fin (r+k) → ℝ in {x | ∀ i,x i ∈ I i}, survivingMixedLimitIntegrand r k x) =
      (∏ j : Fin r, ∫ s in I (Fin.castAdd k j),criticalIntensityDensity c s) *
      ∏ i : Fin k, ∫ t in I (Fin.natAdd r i),tightIntensityDensity t := by
  rw [surviving_mixed_limit_integral_product]
  simp only [surviving_pants_intensity_eq_boundaryFactor,
    surviving_loop_intensity_eq_boundaryFactor,integral_const_mul,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

/-- The actual polynomial contribution (G.6), with the exact ordered label
and flip factors, on arbitrary physical product windows. -/
def survivingMixedCutContribution (P : PsiTheory) (g n r k : ℕ)
    (I : Fin (r+k) → Set ℝ) : ℝ :=
  ((n.descFactorial (2*r):ℝ)/((2:ℝ)^(r+k)*volumeModel P g n))*
    survivingMixedVolumeIntegral P g n r k I

/-- The full numerical assertion for every surviving mixed cut in (G.6).
Both r=0 and k=0, including r=k=0, and degenerate Borel windows are included. -/
lemma surviving_mixed_cut_contribution_tendsto (P : PsiTheory) (n : ℕ → ℕ)
    (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) (r k : ℕ)
    (I : Fin (r+k) → Set ℝ) (hI : ∀ i,MeasurableSet (I i))
    (L : ℝ) (hL : 0 ≤ L) (hIL : ∀ i,I i ⊆ Icc 0 L) :
    Tendsto (fun g => survivingMixedCutContribution P g (n g) r k I) atTop
      (𝓝 ((∏ j : Fin r, ∫ s in I (Fin.castAdd k j),criticalIntensityDensity c s) *
        ∏ i : Fin k, ∫ t in I (Fin.natAdd r i),tightIntensityDensity t)) := by
  have hnTop := surviving_critical_cusps_tendsto n c hc hn
  have hd := surviving_critical_density n c hn
  have ht := (surviving_mixed_prefactor_tendsto P n c hc hn r k).mul
    (surviving_mixed_volume_integral_normalized P n hnTop hd r k I hI L hL hIL)
  rw [surviving_mixed_intensity_integral_product c r k I] at ht
  apply ht.congr'
  filter_upwards [hnTop.eventually_ge_atTop (2*r+1),eventually_ge_atTop (k+1)] with g hng hg
  have hv : volumeModel P (g-k) (n g-r+2*k) ≠ 0 :=
    (diagonal_volume_pos_nonempty P _ _ (by omega) (by unfold Stable;omega)).ne'
  dsimp [survivingMixedPrefactor,survivingMixedCutContribution]
  field_simp

universe u v
/-- The same (G.6) integral for genuine WP boundary volumes, via the existing
classical geometric volume-polynomial bridge, with no numerical volume premise. -/
def survivingMixedGeometricContribution (P : PsiTheory)
    (G : External.WeilPeterssonGeometry.{u,v} P) (g n r k : ℕ)
    (I : Fin (r+k) → Set ℝ) : ℝ :=
  ((n.descFactorial (2*r):ℝ)/((2:ℝ)^(r+k)*External.cuspVolume G g n))*
    ∫ x : Fin (r+k) → ℝ in {x | ∀ i,x i ∈ I i},
      External.wpVolume G (g-k) (n-r+2*k) (survivingBoundaryLengths r k n x)*∏ i,x i

lemma surviving_mixed_geometric_contribution_tendsto (P : PsiTheory)
    (G : External.WeilPeterssonGeometry.{u,v} P) (n : ℕ → ℕ)
    (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) (r k : ℕ)
    (I : Fin (r+k) → Set ℝ) (hI : ∀ i,MeasurableSet (I i))
    (L : ℝ) (hL : 0 ≤ L) (hIL : ∀ i,I i ⊆ Icc 0 L) :
    Tendsto (fun g => survivingMixedGeometricContribution P G g (n g) r k I) atTop
      (𝓝 ((∏ j : Fin r, ∫ s in I (Fin.castAdd k j),criticalIntensityDensity c s) *
        ∏ i : Fin k, ∫ t in I (Fin.natAdd r i),tightIntensityDensity t)) := by
  apply (surviving_mixed_cut_contribution_tendsto P n c hc hn r k I hI L hL hIL).congr'
  have hnTop := surviving_critical_cusps_tendsto n c hc hn
  filter_upwards [hnTop.eventually_ge_atTop (2*r+1),eventually_ge_atTop (k+1)] with g hng hg
  unfold survivingMixedCutContribution survivingMixedGeometricContribution survivingMixedVolumeIntegral
  rw [Geometry.cuspVolume_eq_volumeModel P G g (n g) (by unfold Stable;omega)]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (RandomGeometry.pants_numeric_window_set_measurable _ I hI)] with x hx
  have hs := survivingZeroPad_mem (r+(k+k)) (n g-r+2*k) _ L hL
    (survivingBoundaryCore_mem r k x L (fun i => hIL i (hx i)))
  exact congrArg (fun z : ℝ => z*∏ i,x i)
    (Geometry.wpVolume_eq_boundaryVolumeModel P G (g-k) (n g-r+2*k)
      (survivingBoundaryLengths r k (n g) x) (by unfold Stable;omega) (fun i => (hs i).1)).symm

end WP.Critical
