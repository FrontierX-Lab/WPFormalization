import WPFormalization.Analysis.ChainProfileIntegral

/-! The continuous planar value of the original chain profile.
The vanishing logarithmic term uses the proved quadratic beta/Delta scale,
not a new endpoint convention for the integral. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

lemma chain_oneMinusBeta_logDelta_tendsto :
    Tendsto (fun Y : ℝ => (1-WP.beta Y)*Real.log (4*WP.Delta Y/Real.pi^2))
      (𝓝[<] y₀) (𝓝 0) := by
  have hm : ∀ᶠ Y : ℝ in 𝓝[<] y₀, Y ∈ Ico 0 y₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hy hp
    exact ⟨hp.le,hy⟩
  have hD : Tendsto WP.Delta (𝓝[<] y₀) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨Delta_tendsto_zero_critical,
      hm.mono (fun Y hy => WP.Delta_pos Y hy)⟩
  have hlog : Tendsto (fun Y : ℝ => Real.log (WP.Delta Y)*(WP.Delta Y)^2)
      (𝓝[<] y₀) (𝓝 0) := by
    simpa only [Real.rpow_two,Function.comp_def] using
      (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 2)).comp hD
  have hsq : Tendsto (fun Y : ℝ => (WP.Delta Y)^2) (𝓝[<] y₀) (𝓝 0) := by
    simpa using Delta_tendsto_zero_critical.pow 2
  have hscaled : Tendsto (fun Y : ℝ => (WP.Delta Y)^2*
      Real.log (4*WP.Delta Y/Real.pi^2)) (𝓝[<] y₀) (𝓝 0) := by
    have ht := (hsq.mul_const (Real.log (4/Real.pi^2))).add hlog
    have he : (fun Y : ℝ => (WP.Delta Y)^2*Real.log (4/Real.pi^2)+
        Real.log (WP.Delta Y)*(WP.Delta Y)^2) =ᶠ[𝓝[<] y₀]
        (fun Y : ℝ => (WP.Delta Y)^2*Real.log (4*WP.Delta Y/Real.pi^2)) := by
      filter_upwards [hm] with Y hY
      rw [show 4*WP.Delta Y/Real.pi^2 = (4/Real.pi^2)*WP.Delta Y by ring,
        Real.log_mul (by positivity : 4/Real.pi^2 ≠ 0) (WP.Delta_pos Y hY).ne']
      ring
    simpa using ht.congr' he
  have ht := oneMinusBeta_scaled_tendsto.mul hscaled
  have he : (fun Y : ℝ => ((1-WP.beta Y)/(WP.Delta Y)^2)*
      ((WP.Delta Y)^2*Real.log (4*WP.Delta Y/Real.pi^2))) =ᶠ[𝓝[<] y₀]
      (fun Y : ℝ => (1-WP.beta Y)*Real.log (4*WP.Delta Y/Real.pi^2)) := by
    filter_upwards [hm] with Y hY
    field_simp [(WP.Delta_pos Y hY).ne']
  simpa using ht.congr' he

lemma chainClosedProfileY_tendsto :
    Tendsto chainClosedProfileY (𝓝[<] y₀) (𝓝 (-2*Real.log (2*xCritical))) := by
  unfold chainClosedProfileY
  have hlog := (J_tendsto_critical.const_mul 2).log
    (mul_pos (by norm_num) critical_x_pos).ne'
  simpa only [sub_zero] using
    (hlog.const_mul (-2)).sub chain_oneMinusBeta_logDelta_tendsto

lemma chainProfile_density_tendsto :
    Tendsto (fun l : ℝ => WP.chainProfile (l/(2+l))) atTop
      (𝓝 (-2*Real.log (2*xCritical))) := by
  have ht := chainClosedProfileY_tendsto.comp densityY_tendsto_critical
  have he : (fun l : ℝ => chainClosedProfileY (WP.densityY l)) =ᶠ[atTop]
      (fun l : ℝ => WP.chainProfile (l/(2+l))) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with l hl
    have hs := densityY_spec l hl
    rw [← chainProfile_closed_form_parameter _ hs.1,WP.beta_density_identity _ hs.1,hs.2]
  exact ht.congr' he

end WP.Analysis
