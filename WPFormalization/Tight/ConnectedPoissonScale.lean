import WPFormalization.Tight.ConnectedPoissonModel
import WPFormalization.Tight.ConnectedVariance

noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

lemma connected_tightParameterScale_eq_density (x : ℝ) (hx : x∈Ico (0:ℝ) xCritical) :
    tightParameterScale (inverseY x)=tightScale (2*Psi x) := by
  unfold tightScale
  rw [show 2*Psi x=density (inverseY x) by unfold Psi;ring,
    Analysis.volume_profile_inverse_density _ (inverseY_branch x hx).1]
  rfl

lemma connected_tightScale_ratio_at_zero (ls ms : ℕ→ℝ)
    (hl : Tendsto ls atTop (𝓝 0)) (hm : Tendsto ms atTop (𝓝 0))
    (hl0 : ∀ᶠ j in atTop,0 ≤ ls j) (hm0 : ∀ᶠ j in atTop,0 ≤ ms j) :
    Tendsto (fun j=>tightScale (ls j)/tightScale (ms j)) atTop (𝓝 1) := by
  have hzero : Tendsto (fun j=>2*|ls j-ms j|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero,mul_zero] using ((hl.sub hm).abs.const_mul 2)
  have hlog : Tendsto (fun j=>Real.log (tightScale (ls j))-Real.log (tightScale (ms j)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hzero
    filter_upwards [hl0,hm0] with j hj hk
    have hbound := tightScale_log_comparison (ls j) (ms j) hj hk
    have hden : 1≤1+min (ls j) (ms j) := by simp only [le_add_iff_nonneg_right];exact le_min hj hk
    exact hbound.trans (div_le_self (by positivity) hden)
  have ht := Real.continuous_exp.continuousAt.tendsto.comp hlog
  simp only [Real.exp_zero] at ht
  apply ht.congr'
  filter_upwards [hl0,hm0] with j hj hk
  dsimp only [Function.comp_def]
  rw [Real.exp_sub,Real.exp_log (tightScale_pos _ hj),Real.exp_log (tightScale_pos _ hk)]

lemma connected_bounded_poisson_scale_ratio_tendsto (gs : ℕ→ℕ)
    (hg : Tendsto gs atTop atTop) (n : ℕ) (c : ℝ) (hc : 0<c) :
    Tendsto (fun j=>tightParameterScale (inverseY (c/(complexity (gs j) 0:ℝ)))/
      tightScale ((n:ℝ)/(gs j:ℝ))) atTop (𝓝 1) := by
  let hs : ℕ→ℝ := fun j=>(complexity (gs j) 0:ℝ)
  have hh := connected_complexity_tendsto gs hg
  have hx := connected_small_weight_tendsto hs hh c
  have hp0 : Tendsto (fun j=>2*Psi (c/hs j)) atTop (𝓝 0) := by
    have hP := (Analysis.Psi_analyticAt_interior 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩).continuousAt.tendsto.comp hx
    simpa only [Analysis.Psi_zero_value,mul_zero,Function.comp_def] using hP.const_mul 2
  have hn0 : Tendsto (fun j=>(n:ℝ)/(gs j:ℝ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp hg).const_div_atTop _
  have hxd : ∀ᶠ j in atTop,c/hs j∈Ioo (0:ℝ) xCritical := by
    filter_upwards [hh.eventually_gt_atTop 0,connected_small_weight_eventually hs hh c hc.le] with j hj hk
    exact ⟨div_pos hc hj,hk.2⟩
  have hnon : ∀ᶠ j in atTop,0≤2*Psi (c/hs j) := hxd.mono (fun j hj=>by
    have hp := (connected_variance_formula _ hj).1
    positivity)
  have ht := connected_tightScale_ratio_at_zero _ _ hp0 hn0 hnon
    (Eventually.of_forall (fun j=>by positivity))
  apply ht.congr'
  filter_upwards [hxd] with j hj
  rw [connected_tightParameterScale_eq_density _ ⟨hj.1.le,hj.2⟩]

lemma connected_origin_parameter_scale_ratio_tendsto (hs : ℕ→ℝ)
    (hh : Tendsto hs atTop atTop) (c d : ℝ) (hc : 0≤c) (hd : 0≤d) :
    Tendsto (fun j=>tightParameterScale (inverseY (c/hs j))/
      tightParameterScale (inverseY (d/hs j))) atTop (𝓝 1) := by
  have hlim (b : ℝ) : Tendsto (fun j=>2*Psi (b/hs j)) atTop (𝓝 0) := by
    have ht := (Analysis.Psi_analyticAt_interior 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩).continuousAt.tendsto.comp
      (connected_small_weight_tendsto hs hh b)
    simpa only [Analysis.Psi_zero_value,mul_zero,Function.comp_def] using ht.const_mul 2
  have hnon (b : ℝ) (hb : 0≤b) : ∀ᶠ j in atTop,0≤2*Psi (b/hs j) := by
    filter_upwards [connected_small_weight_eventually hs hh b hb] with j hj
    have hdens := density_nonneg _ (inverseY_branch _ hj).1
    unfold Psi
    linarith
  have ht := connected_tightScale_ratio_at_zero _ _ (hlim c) (hlim d) (hnon c hc) (hnon d hd)
  apply ht.congr'
  filter_upwards [connected_small_weight_eventually hs hh c hc,
    connected_small_weight_eventually hs hh d hd] with j hj hk
  rw [connected_tightParameterScale_eq_density _ hj,connected_tightParameterScale_eq_density _ hk]

end WP.TightConnected
