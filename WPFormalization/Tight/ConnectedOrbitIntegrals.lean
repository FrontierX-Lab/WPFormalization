import WPFormalization.Tight.ConnectedOrbitCoefficients
noncomputable section
namespace WP.TightConnected
open Set Filter Finset External MeasureTheory
open scoped Topology BigOperators ENNReal
lemma tightIntensityDensity_continuous : Continuous tightIntensityDensity := by
  have hb : Continuous (boundaryFactor 0) := by
    have hh := boundaryFactor_joint_continuous.comp
      (show Continuous (fun t : ℝ=>((⟨0,le_rfl,y₀_pos.le⟩ : Icc (0:ℝ) y₀),t)) from
        continuous_const.prodMk continuous_id)
    exact hh
  have he : tightIntensityDensity = fun t=>(1/2:ℝ)*(t*boundaryFactor 0 t^2) :=
    funext Critical.surviving_loop_intensity_eq_boundaryFactor
  rw [he]
  exact continuous_const.mul (continuous_id.mul (hb.pow 2))

lemma connected_cut_scaled_coefficient_density_tendsto (P : PsiTheory) (k : ℕ)
    (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (Ds : ℕ→MulticurveCutData 0 k) (hcs : ∀j,(Ds j).components=1)
    (cs : (j:ℕ)→Fin (Ds j).components)
    (B : ℝ) (hB : 0≤B) (x : Fin k→ℝ) (hx : ∀i,x i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>connectedCutScaledCoefficientDensity P k (gs j) (ns j) (Ds j) (hcs j) (cs j) x)
      atTop (𝓝 (∏i,tightIntensityDensity (x i))) := by
  have hr : Tendsto (fun j=>connectedDensityCoefficientRatio P k (gs j) (ns j)
      (connected_cut_boundaryVector k (Ds j) (hcs j) (cs j) x)) atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := tight_connected P k B hB (ε/2) (half_pos hε)
    filter_upwards [hgs.eventually_ge_atTop N] with j hj
    exact (hN (gs j) hj (ns j) _
      (connected_cut_boundaryVector_mem k (Ds j) (hcs j) (cs j) x B hx)).trans_lt (half_lt_self hε)
  simp_rw [connected_cut_scaled_coefficient_density_eq_ratio]
  simpa only [one_mul] using hr.mul_const (∏i,tightIntensityDensity (x i))

lemma connected_cut_scaled_coefficient_integral_tendsto (P : PsiTheory) (k : ℕ)
    (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (Ds : ℕ→MulticurveCutData 0 k) (hcs : ∀j,(Ds j).components=1)
    (cs : (j:ℕ)→Fin (Ds j).components)
    (I : Fin k→Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (B : ℝ) (hB : 0≤B) (hIB : ∀i,I i⊆Icc (0:ℝ) B) :
    Tendsto (fun j=>∫ x : Fin k→ℝ in {x|∀i,x i∈I i},
      connectedCutScaledCoefficientDensity P k (gs j) (ns j) (Ds j) (hcs j) (cs j) x)
      atTop (𝓝 (∏i,∫t in I i,tightIntensityDensity t)) := by
  let W : Set (Fin k→ℝ) := {x|∀i,x i∈I i}
  let H : (Fin k→ℝ)→ℝ := fun x=>∏i,tightIntensityDensity (x i)
  let F : ℕ→(Fin k→ℝ)→ℝ := fun j=>
    connectedCutScaledCoefficientDensity P k (gs j) (ns j) (Ds j) (hcs j) (cs j)
  have hW : MeasurableSet W := RandomGeometry.pants_numeric_window_set_measurable k I hI
  have hH : Continuous H := by
    exact continuous_finsetProd _ (fun i _=>tightIntensityDensity_continuous.comp (continuous_apply i))
  have hmeas : ∀ᶠj in atTop,AEStronglyMeasurable (F j) (volume.restrict W) :=
    Eventually.of_forall fun j=>
      (connected_cut_scaled_coefficient_density_continuous P k (gs j) (ns j) (Ds j) (hcs j) (cs j)).aestronglyMeasurable
  have hb : Integrable (fun x=>2*‖H x‖) (volume.restrict W) :=
    RandomGeometry.pants_window_integrable_continuous k I B hIB _
      (continuous_const.mul hH.norm)
  have hbound : ∀ᶠj in atTop,∀ᵐx ∂volume.restrict W,‖F j x‖≤2*‖H x‖ := by
    obtain ⟨N,hN⟩ := tight_connected P k B hB 1 zero_lt_one
    filter_upwards [hgs.eventually_ge_atTop N] with j hj
    filter_upwards [ae_restrict_mem hW] with x hx
    have hr := hN (gs j) hj (ns j) _
      (connected_cut_boundaryVector_mem k (Ds j) (hcs j) (cs j) x B (fun i=>hIB i (hx i)))
    have hra : |connectedDensityCoefficientRatio P k (gs j) (ns j)
        (connected_cut_boundaryVector k (Ds j) (hcs j) (cs j) x)|≤2 := by
      have ht := abs_add_le
        (connectedDensityCoefficientRatio P k (gs j) (ns j)
          (connected_cut_boundaryVector k (Ds j) (hcs j) (cs j) x)-1) 1
      simp only [sub_add_cancel,abs_one] at ht
      linarith
    dsimp only [F,H]
    rw [connected_cut_scaled_coefficient_density_eq_ratio,norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hra (norm_nonneg _)
  have hpoint : ∀ᵐx ∂volume.restrict W,Tendsto (fun j=>F j x) atTop (𝓝 (H x)) := by
    filter_upwards [ae_restrict_mem hW] with x hx
    exact connected_cut_scaled_coefficient_density_tendsto P k gs ns hgs Ds hcs cs B hB x
      (fun i=>hIB i (hx i))
  have ht := tendsto_integral_filter_of_dominated_convergence (fun x=>2*‖H x‖) hmeas hbound hb hpoint
  have hprod : (∫x in W,H x)=∏i,∫t in I i,tightIntensityDensity t := by
    have hw : W=Set.univ.pi I := by ext x;simp [W]
    rw [hw,volume_pi,Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (fun _ : Fin k=>tightIntensityDensity)
  rw [hprod] at ht
  exact ht


end WP.TightConnected
