import WPFormalization.Critical.SurvivingMixedVolume

/-! The numerical density integrals are the already defined genuine Borel
intensity masses. No positive-width or nonzero-mass restriction is imposed. -/
noncomputable section
namespace WP.Critical
open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false in
lemma surviving_boundaryFactor_zero_continuous : Continuous (boundaryFactor 0) := by
  let Y : Icc (0:ℝ) y₀ := ⟨0,le_rfl,y₀_pos.le⟩
  have hh : Continuous (fun t : ℝ => ((Y,t) : (Icc (0:ℝ) y₀) × ℝ)) :=
    continuous_const.prodMk continuous_id
  have h := boundaryFactor_joint_continuous.comp hh
  change Continuous (boundaryFactor 0) at h
  exact h

lemma surviving_criticalIntensityDensity_continuous (c : ℝ) :
    Continuous (criticalIntensityDensity c) := by
  unfold criticalIntensityDensity
  fun_prop

lemma surviving_tightIntensityDensity_continuous : Continuous tightIntensityDensity := by
  have he : tightIntensityDensity = fun t : ℝ => (1/2:ℝ)*(t*boundaryFactor 0 t^2) :=
    funext surviving_loop_intensity_eq_boundaryFactor
  rw [he]
  exact continuous_const.mul (continuous_id.mul (surviving_boundaryFactor_zero_continuous.pow 2))

lemma surviving_criticalIntensityDensity_nonneg (c t : ℝ) (ht : 0 ≤ t) :
    0 ≤ criticalIntensityDensity c t := by
  rw [surviving_pants_intensity_eq_boundaryFactor]
  exact mul_nonneg (by positivity) (mul_nonneg ht (boundaryFactor_pos 0 t).le)

lemma surviving_tightIntensityDensity_nonneg (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ tightIntensityDensity t := by
  rw [surviving_loop_intensity_eq_boundaryFactor]
  positivity

lemma surviving_bounded_density_integrable (f : ℝ → ℝ) (hf : Continuous f)
    (I : Set ℝ) (L : ℝ) (hIL : I ⊆ Icc 0 L) : IntegrableOn f I :=
  hf.integrableOn_Icc.mono_set hIL

lemma surviving_bounded_density_measure (f : ℝ → ℝ) (hf : Continuous f)
    (I : Set ℝ) (hI : MeasurableSet I) (L : ℝ) (hIL : I ⊆ Icc 0 L)
    (hf0 : ∀ t ∈ I,0 ≤ f t) :
    ((volume.restrict (Ici (0:ℝ))).withDensity (fun t => ENNReal.ofReal (f t))) I =
      ENNReal.ofReal (∫ t in I,f t) := by
  rw [withDensity_apply _ hI,Measure.restrict_restrict hI]
  rw [inter_eq_left.mpr (show I ⊆ Ici 0 from fun t ht => (hIL ht).1)]
  exact (ofReal_integral_eq_lintegral_ofReal
    (surviving_bounded_density_integrable f hf I L hIL)
    (by filter_upwards [ae_restrict_mem hI] with t ht;exact hf0 t ht)).symm

lemma surviving_criticalIntensity_apply (c : ℝ) (I : Set ℝ) (hI : MeasurableSet I)
    (L : ℝ) (hIL : I ⊆ Icc 0 L) :
    criticalIntensity c I = ENNReal.ofReal (∫ s in I,criticalIntensityDensity c s) :=
  surviving_bounded_density_measure _ (surviving_criticalIntensityDensity_continuous c)
    I hI L hIL (fun t ht => surviving_criticalIntensityDensity_nonneg c t (hIL ht).1)

lemma surviving_tightIntensity_apply (I : Set ℝ) (hI : MeasurableSet I)
    (L : ℝ) (hIL : I ⊆ Icc 0 L) :
    tightIntensity I = ENNReal.ofReal (∫ t in I,tightIntensityDensity t) :=
  surviving_bounded_density_measure _ surviving_tightIntensityDensity_continuous
    I hI L hIL (fun t ht => surviving_tightIntensityDensity_nonneg t (hIL ht).1)

lemma surviving_criticalIntensity_toReal (c : ℝ) (I : Set ℝ) (hI : MeasurableSet I)
    (L : ℝ) (hIL : I ⊆ Icc 0 L) :
    (criticalIntensity c I).toReal = ∫ s in I,criticalIntensityDensity c s := by
  rw [surviving_criticalIntensity_apply c I hI L hIL,ENNReal.toReal_ofReal]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem hI] with t ht
  exact surviving_criticalIntensityDensity_nonneg c t (hIL ht).1

lemma surviving_tightIntensity_toReal (I : Set ℝ) (hI : MeasurableSet I)
    (L : ℝ) (hIL : I ⊆ Icc 0 L) :
    (tightIntensity I).toReal = ∫ t in I,tightIntensityDensity t := by
  rw [surviving_tightIntensity_apply I hI L hIL,ENNReal.toReal_ofReal]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem hI] with t ht
  exact surviving_tightIntensityDensity_nonneg t (hIL ht).1

lemma surviving_criticalIntensity_lt_top (c : ℝ) (I : Set ℝ) (hI : MeasurableSet I)
    (L : ℝ) (hIL : I ⊆ Icc 0 L) : criticalIntensity c I < ⊤ := by
  rw [surviving_criticalIntensity_apply c I hI L hIL]
  exact ENNReal.ofReal_lt_top

lemma surviving_tightIntensity_lt_top (I : Set ℝ) (hI : MeasurableSet I)
    (L : ℝ) (hIL : I ⊆ Icc 0 L) : tightIntensity I < ⊤ := by
  rw [surviving_tightIntensity_apply I hI L hIL]
  exact ENNReal.ofReal_lt_top

lemma surviving_mixed_cut_contribution_measure_tendsto (P : PsiTheory) (n : ℕ → ℕ)
    (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) (r k : ℕ)
    (I : Fin (r+k) → Set ℝ) (hI : ∀ i,MeasurableSet (I i))
    (L : ℝ) (hL : 0 ≤ L) (hIL : ∀ i,I i ⊆ Icc 0 L) :
    Tendsto (fun g => survivingMixedCutContribution P g (n g) r k I) atTop
      (𝓝 ((∏ j : Fin r,(criticalIntensity c (I (Fin.castAdd k j))).toReal) *
        ∏ i : Fin k,(tightIntensity (I (Fin.natAdd r i))).toReal)) := by
  simpa only [surviving_criticalIntensity_toReal c _ (hI _) L (hIL _),
    surviving_tightIntensity_toReal _ (hI _) L (hIL _)] using
      surviving_mixed_cut_contribution_tendsto P n c hc hn r k I hI L hL hIL

universe u v
lemma surviving_mixed_geometric_contribution_measure_tendsto (P : PsiTheory)
    (G : External.WeilPeterssonGeometry.{u,v} P) (n : ℕ → ℕ)
    (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) (r k : ℕ)
    (I : Fin (r+k) → Set ℝ) (hI : ∀ i,MeasurableSet (I i))
    (L : ℝ) (hL : 0 ≤ L) (hIL : ∀ i,I i ⊆ Icc 0 L) :
    Tendsto (fun g => survivingMixedGeometricContribution P G g (n g) r k I) atTop
      (𝓝 ((∏ j : Fin r,(criticalIntensity c (I (Fin.castAdd k j))).toReal) *
        ∏ i : Fin k,(tightIntensity (I (Fin.natAdd r i))).toReal)) := by
  simpa only [surviving_criticalIntensity_toReal c _ (hI _) L (hIL _),
    surviving_tightIntensity_toReal _ (hI _) L (hIL _)] using
      surviving_mixed_geometric_contribution_tendsto P G n c hc hn r k I hI L hL hIL

end WP.Critical
