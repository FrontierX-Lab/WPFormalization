import WPFormalization.Coefficients.SaddleActionRegularity
import WPFormalization.Analysis.LogarithmicLegendreDefect
/-! Quadratic logarithmic saddle defect for the actual unscaled degree kernel. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Set
lemma unscaled_logarithmic_legendre_defect_bound:
    ∃B:ℝ,0 < B∧∀z∈Icc (0:ℝ) (r 0),
      unscaledLogPotential (r 0)-unscaledLogPotential z-
        unscaledMean z*(Real.log (r 0)-Real.log z) ≤ B*(3/2-unscaledMean z)^2:=by
  obtain ⟨C,hC,hμB⟩:=unscaledMean_uniform_linear_variance_bounds
  have hF:∀t∈Icc (0:ℝ) (r 0),DifferentiableAt ℝ unscaledLogPotential t:=
    fun t ht=>(unscaledLogPotential_hasDerivAt t ht).differentiableAt
  have hμ:∀t∈Icc (0:ℝ) (r 0),DifferentiableAt ℝ unscaledMean t:=
    fun t ht=>(unscaledMean_hasDerivAt t ht).differentiableAt
  have hμeq:∀t∈Icc (0:ℝ) (r 0),unscaledMean t=t*deriv unscaledLogPotential t:=by
    intro t ht
    rw[(unscaledLogPotential_hasDerivAt t ht).deriv,unscaledMean_eq_logSlope]
  have hc:ContinuousOn (Analysis.logarithmicLegendreDefect unscaledLogPotential unscaledMean (r 0))
      (Icc (0:ℝ) (r 0)):=by
    obtain ⟨R,hR,hzero⟩:=unscaled_kernel_zero_free_radius
    have hL:ContinuousOn (fun z:ℝ=>(kernelLogSlope (z:ℂ)).re) (Icc (0:ℝ) (r 0)):=by
      intro z hz
      have hzn:‖(z:ℂ)‖ < R:=by
        rw[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1]
        exact hz.2.trans_lt hR
      exact (Complex.continuous_re.continuousAt.comp
        ((kernelLogSlope_analyticAt R (fun w hw=>hzero w hw.le) (z:ℂ) hzn).continuousAt.comp
          Complex.continuous_ofReal.continuousAt)).continuousWithinAt
    have hFc:ContinuousOn unscaledLogPotential (Icc (0:ℝ) (r 0)):=
      fun t ht=>(hF t ht).continuousAt.continuousWithinAt
    have hμc:ContinuousOn unscaledMean (Icc (0:ℝ) (r 0)):=
      fun t ht=>(hμ t ht).continuousAt.continuousWithinAt
    have he:Analysis.logarithmicLegendreDefect unscaledLogPotential unscaledMean (r 0)=
        fun z=>unscaledLogPotential (r 0)-unscaledLogPotential z-
          unscaledMean z*Real.log (r 0)+(kernelLogSlope (z:ℂ)).re*(z*Real.log z):=by
      funext z
      dsimp[Analysis.logarithmicLegendreDefect]
      rw[unscaledMean_eq_logSlope]
      ring
    rw[he]
    exact ((continuousOn_const.sub hFc).sub (hμc.mul continuousOn_const)).add
      (hL.mul Real.continuous_mul_log.continuousOn)
  obtain ⟨B,hB,hb⟩:=Analysis.logarithmicLegendreDefect_uniform_quadratic
    unscaledLogPotential unscaledMean (r 0) C (r_pos 0 ⟨le_rfl,y₀_pos⟩) hC hF hμ hμeq
    (fun t ht=>⟨(hμB t ht).2.2.1,(hμB t ht).2.2.2⟩) hc
  refine ⟨B,hB,?_⟩
  intro z hz
  simpa only[Analysis.logarithmicLegendreDefect,unscaledMean_at_r] using hb z hz
end WP.Coefficients
