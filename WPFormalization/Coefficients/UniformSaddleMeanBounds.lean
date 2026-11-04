import WPFormalization.Coefficients.UniformSaddleMean
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: MeanBounds. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology
lemma unscaledMean_eq_logSlope (z:ℝ):unscaledMean z=z*(kernelLogSlope (z:ℂ)).re:=by
  rw[←kernelComplexMean_re]
  simp only[kernelComplexMean,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
lemma unscaledMean_lower_linear (z:ℝ)(hz:z∈Icc (0:ℝ) (r 0)):z/5≤ unscaledMean z:=by
  obtain ⟨R,hR,hzero⟩:=unscaled_kernel_zero_free_radius
  have hdiff:DifferentiableOn ℂ kernelLogSlope (Metric.ball 0 R):=by
    intro w hw
    exact (kernelLogSlope_analyticAt R (fun w hw=>hzero w hw.le) w
      (by simpa only[Metric.mem_ball,dist_zero_right] using hw)).differentiableAt.differentiableWithinAt
  have hzn:‖(z:ℂ)‖<R:=by rw[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1];exact hz.2.trans_lt hR
  have hs:=Analysis.hasSum_coeff_on_ball kernelLogSlope R hdiff (z:ℂ) hzn
  have hsR:HasSum (fun n:ℕ=>realCoeff kernelLogSlope n*z^n) (kernelLogSlope (z:ℂ)).re:=by
    convert Complex.hasSum_re hs using 1
    ext n
    simp only[←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,realCoeff]
  have hlo:=hsR.summable.le_tsum 0 (fun n _=>mul_nonneg (kernelLogSlope_coeff_pos n).le (pow_nonneg hz.1 _))
  rw[hsR.tsum_eq,pow_zero,mul_one] at hlo
  have hfirst:realCoeff kernelLogSlope 0=1/5:=by
    simp only[realCoeff,WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,kernelLogSlope_zero]
    norm_num
  rw[hfirst] at hlo
  rw[unscaledMean_eq_logSlope]
  nlinarith[mul_le_mul_of_nonneg_left hlo hz.1]
lemma unscaledMean_uniform_linear_variance_bounds:
    ∃C:ℝ,0<C∧∀z∈Icc (0:ℝ) (r 0),z/5≤ unscaledMean z∧unscaledMean z≤ C*z∧
      1/5≤ deriv unscaledMean z∧deriv unscaledMean z≤ C:=by
  obtain ⟨R,hR,hzero⟩:=unscaled_kernel_zero_free_radius
  have hr:0<r 0:=r_pos 0 ⟨le_rfl,y₀_pos⟩
  let F:ℝ→ℝ:=fun z=>‖kernelLogSlope (z:ℂ)‖+‖deriv kernelComplexMean (z:ℂ)‖
  have hcont:ContinuousOn F (Icc (0:ℝ) (r 0)):=by
    intro z hz
    have hzn:‖(z:ℂ)‖<R:=by rw[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1];exact hz.2.trans_lt hR
    have hL:=kernelLogSlope_analyticAt R (fun w hw=>hzero w hw.le) (z:ℂ) hzn
    have hM:=kernelComplexMean_analyticAt R (fun w hw=>hzero w hw.le) (z:ℂ) hzn
    exact (((hL.continuousAt.comp Complex.continuous_ofReal.continuousAt).norm).add
      ((hM.deriv.continuousAt.comp Complex.continuous_ofReal.continuousAt).norm)).continuousWithinAt
  obtain ⟨z₀,hz₀,hmax⟩:=isCompact_Icc.exists_isMaxOn (f:=F) ⟨0,le_rfl,hr.le⟩ hcont
  let C:ℝ:=F z₀+1
  have hC:0<C:=by dsimp[C,F];positivity
  refine ⟨C,hC,?_⟩
  intro z hz
  have hf:F z≤ F z₀:=(isMaxOn_iff.mp hmax) z hz
  have hL:‖kernelLogSlope (z:ℂ)‖≤ C:=by
    dsimp[F,C] at *
    linarith[norm_nonneg (deriv kernelComplexMean (z:ℂ))]
  have hM:‖deriv kernelComplexMean (z:ℂ)‖≤ C:=by
    dsimp[F,C] at *
    linarith[norm_nonneg (kernelLogSlope (z:ℂ))]
  refine ⟨unscaledMean_lower_linear z hz,?_,unscaledMean_deriv_lower z hz,?_⟩
  · rw[unscaledMean_eq_logSlope]
    have hh:(kernelLogSlope (z:ℂ)).re≤ C:=(Complex.re_le_norm _).trans hL
    nlinarith[mul_le_mul_of_nonneg_left hh hz.1]
  · rw[(unscaledMean_hasDerivAt z hz).deriv]
    exact (Complex.re_le_norm _).trans hM
lemma saddleZeta_le_five_mul (u:ℝ)(hu:u∈Icc (0:ℝ) (3/2)):
    saddleZeta u≤5*u:=by
  have hs:=saddleZeta_spec u hu
  have hl:=unscaledMean_lower_linear _ hs.1
  rw[hs.2] at hl
  linarith
lemma saddleZeta_tendsto_zero_right:
    Tendsto saddleZeta (𝓝[≥] (0:ℝ)) (𝓝 (0:ℝ)):=by
  have hT:Tendsto (fun u:ℝ=>5*u) (𝓝[≥] (0:ℝ)) (𝓝 (0:ℝ)):=by
    have hc:Continuous (fun u:ℝ=>5*u):=continuous_const.mul continuous_id
    simpa only[mul_zero] using (hc.continuousAt.tendsto (x:=(0:ℝ))).mono_left nhdsWithin_le_nhds
  have he:∀ᶠu:ℝ in 𝓝[≥] (0:ℝ),u∈Icc (0:ℝ) (3/2):=by
    filter_upwards[self_mem_nhdsWithin,(eventually_lt_nhds (by norm_num:(0:ℝ)<3/2)).filter_mono nhdsWithin_le_nhds] with u hu hU
    exact ⟨hu,hU.le⟩
  exact squeeze_zero' (he.mono (fun u hu=>(saddleZeta_spec u hu).1.1))
    (he.mono (fun u hu=>saddleZeta_le_five_mul u hu)) hT
end WP.Coefficients
