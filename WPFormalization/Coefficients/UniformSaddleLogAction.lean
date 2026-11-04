import WPFormalization.Coefficients.UniformSaddleMean
import WPFormalization.Analysis.RealPrimitiveDerivative
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: LogAction. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology
lemma H_zero_deriv_real (z:ℝ):deriv (H 0) (z:ℂ)=((deriv (H 0) (z:ℂ)).re:ℂ):=by
  have hi:=deriv_im_eq_zero_of_real_axis (H 0) (H_differentiable 0)
    (fun t=>by rw[H_zero_real t];exact Complex.ofReal_im _) z
  apply Complex.ext
  · rfl
  · simpa only[Complex.ofReal_im] using hi
lemma kernelLogSlope_real (z:ℝ):kernelLogSlope (z:ℂ)=
    ((-(deriv (H 0) (z:ℂ)).re/(H 0 (z:ℂ)).re:ℝ):ℂ):=by
  unfold kernelLogSlope
  rw[H_zero_deriv_real z,H_zero_real z]
  simp only[Complex.ofReal_re,Complex.ofReal_div,Complex.ofReal_neg]
lemma unscaled_kernel_log_action:
    ∃(R:ℝ)(S:ℂ→ℂ),r 0<R∧AnalyticOnNhd ℂ S (Metric.ball 0 R)∧
      S 0=0∧deriv S 0=1/5∧
      (∀w∈Metric.ball (0:ℂ) R,HasDerivAt S (kernelLogSlope w) w)∧
      (∀z:ℝ,z∈Icc (0:ℝ) (r 0)→S (z:ℂ)=((-Real.log (H 0 z).re:ℝ):ℂ))∧
      ∀w∈Metric.ball (0:ℂ) R,Complex.exp (S w)=(H 0 w)⁻¹:=by
  obtain ⟨R,hR,hzero⟩:=unscaled_kernel_zero_free_radius
  have hr:0<r 0:=r_pos 0 ⟨le_rfl,y₀_pos⟩
  have hRp:0<R:=hr.trans hR
  let f:ℝ→ℝ:=fun z=>-Real.log (H 0 z).re
  have hf:ContinuousOn f (Icc (0:ℝ) (r 0)):=by
    intro z hz
    have hc:ContinuousAt (fun t:ℝ=>(H 0 (t:ℂ)).re) z:=
      Complex.continuous_re.continuousAt.comp ((H_differentiable 0 (z:ℂ)).continuousAt.comp Complex.continuous_ofReal.continuousAt)
    exact (hc.log (H_zero_re_pos z hz).ne').neg.continuousWithinAt
  have hLa:AnalyticOnNhd ℂ kernelLogSlope (Metric.ball 0 R):=by
    intro z hz
    exact kernelLogSlope_analyticAt R (fun w hw=>hzero w hw.le) z (by simpa only[Metric.mem_ball,dist_zero_right] using hz)
  have hdf:∀z∈Ioo (0:ℝ) (r 0),HasDerivAt (fun t:ℝ=>(f t:ℂ)) (kernelLogSlope (z:ℂ)) z:=by
    intro z hz
    have hdH:=Complex.reCLM.hasFDerivAt.comp_hasDerivAt z (H_differentiable 0 (z:ℂ)).hasDerivAt.comp_ofReal
    have hdF:HasDerivAt f (-((deriv (H 0) (z:ℂ)).re/(H 0 (z:ℂ)).re)) z:=
      (hdH.log (H_zero_re_pos z ⟨hz.1.le,hz.2.le⟩).ne').neg
    convert! hdF.ofReal_comp using 1
    rw[kernelLogSlope_real]
    push_cast
    ring
  obtain ⟨S,hSa,hSd,hreal⟩:=Analysis.real_primitive_complex_extension_with_derivative_on_ball
    0 (r 0) hr f hf (Metric.ball 0 R) kernelLogSlope hLa hdf 0 ⟨le_rfl,hr.le⟩ R hRp (Subset.refl _)
  have hzeroB:(0:ℂ)∈Metric.ball 0 R:=Metric.mem_ball_self hRp
  have hS0:S 0=0:=by
    have he:=hreal 0 ⟨le_rfl,hr.le⟩ (by simpa only[Complex.ofReal_zero] using hzeroB)
    simpa only[Complex.ofReal_zero,f,H_zero,Analysis.derivX_zero,Complex.one_re,Real.log_one,neg_zero] using he
  have hSd0:deriv S 0=1/5:=(hSd 0 hzeroB).deriv.trans kernelLogSlope_zero
  have hreal':∀z:ℝ,z∈Icc (0:ℝ) (r 0)→S (z:ℂ)=((-Real.log (H 0 z).re:ℝ):ℂ):=by
    intro z hz
    exact hreal z hz (by rw[Complex.ofReal_zero,Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1];exact hz.2.trans_lt hR)
  let F:ℂ→ℂ:=fun w=>Complex.exp (S w)*H 0 w
  have hFder:∀w∈Metric.ball (0:ℂ) R,HasDerivAt F 0 w:=by
    intro w hw
    have hn:H 0 w≠0:=hzero w (by simpa only[Metric.mem_ball,dist_zero_right] using hw : ‖w‖<R).le
    convert! ((hSd w hw).cexp).mul (H_differentiable 0 w).hasDerivAt using 1
    dsimp[kernelLogSlope]
    field_simp
    <;>ring
  have hFdiff:DifferentiableOn ℂ F (Metric.ball 0 R):=fun w hw=>(hFder w hw).differentiableAt.differentiableWithinAt
  refine ⟨R,S,hR,hSa,hS0,hSd0,hSd,hreal',?_⟩
  intro w hw
  have he:=Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0:ℂ) R).isPreconnected
    hFdiff (fun w hw=>(hFder w hw).deriv) hw hzeroB
  have he':Complex.exp (S w)*H 0 w=1:=by
    simpa only[F,hS0,Complex.exp_zero,H_zero,Analysis.derivX_zero,one_mul] using he
  have hn:H 0 w≠0:=hzero w (by simpa only[Metric.mem_ball,dist_zero_right] using hw : ‖w‖<R).le
  field_simp
  exact he'
end WP.Coefficients
