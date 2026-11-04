import WPFormalization.Coefficients.UniformSaddleMean
import WPFormalization.Analysis.TaylorReality
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: Probability. -/
noncomputable section
namespace WP.Coefficients
open Set
lemma unscaled_negative_power_realCoefficients (h:ℕ):
    Analysis.RealCoefficients (fun w:ℂ=>(H 0 w)⁻¹^h):=by
  have hH:AnalyticAt ℂ (H 0) 0:=(H_differentiable 0).analyticAt 0
  have hH0:H 0 0≠0:=by rw[H_zero,Analysis.derivX_zero];norm_num
  exact Analysis.realCoefficients_pow (hH.inv hH0)
    (Analysis.realCoefficients_inv hH hH0 (Analysis.H_realCoefficients_ofReal 0)) h
lemma unscaledCoeff_complex (h m:ℕ):
    WP.coeff (fun w:ℂ=>(H 0 w)⁻¹^h) m=(unscaledCoeff h m:ℂ):=by
  apply Complex.ext
  · rfl
  · simpa only[Complex.ofReal_im] using unscaled_negative_power_realCoefficients h m
lemma unscaledCoeff_hasSum (h:ℕ)(z:ℂ)(hz:‖z‖≤ r 0):
    HasSum (fun m:ℕ=>(unscaledCoeff h m:ℂ)*z^m) ((H 0 z)⁻¹^h):=by
  obtain ⟨R,hR,hzero⟩:=unscaled_kernel_zero_free_radius
  have hf:DifferentiableOn ℂ (fun w:ℂ=>(H 0 w)⁻¹^h) (Metric.ball 0 R):=by
    intro w hw
    exact (((H_differentiable 0 w).inv (hzero w (show ‖w‖<R by simpa only[Metric.mem_ball,dist_zero_right] using hw).le)).pow h).differentiableWithinAt
  have hs:=Analysis.hasSum_coeff_on_ball (fun w:ℂ=>(H 0 w)⁻¹^h) R hf z (hz.trans_lt hR)
  simpa only[unscaledCoeff_complex] using hs
lemma tiltedKernelMass_nonneg (z:ℝ)(hz:z∈Icc (0:ℝ) (r 0))(h m:ℕ)(hh:0<h):
    0≤ tiltedKernelMass z h m:=by
  rw[tiltedKernelMass_eq_unscaled]
  exact mul_nonneg (mul_nonneg (pow_nonneg (H_zero_re_pos z hz).le _) (pow_nonneg hz.1 _)) (unscaledCoeff_pos h m hh).le
lemma tiltedKernelMass_pos (z:ℝ)(hz:0<z)(hzr:z≤ r 0)(h m:ℕ)(hh:0<h):
    0<tiltedKernelMass z h m:=by
  rw[tiltedKernelMass_eq_unscaled]
  exact mul_pos (mul_pos (pow_pos (H_zero_re_pos z ⟨hz.le,hzr⟩) _) (pow_pos hz _)) (unscaledCoeff_pos h m hh)
lemma tiltedKernelMass_hasSum (z:ℝ)(hz:z∈Icc (0:ℝ) (r 0))(h:ℕ):
    HasSum (tiltedKernelMass z h) 1:=by
  have hzn:‖(z:ℂ)‖≤ r 0:=by rw[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1];exact hz.2
  have hs:=Complex.hasSum_re (unscaledCoeff_hasSum h (z:ℂ) hzn)
  have hsR:HasSum (fun m:ℕ=>unscaledCoeff h m*z^m) ((H 0 z).re⁻¹^h):=by
    convert hs using 1
    · ext m
      simp only[←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    · rw[H_zero_real z,←Complex.ofReal_inv,←Complex.ofReal_pow,Complex.ofReal_re]
      simp only[Complex.ofReal_re]
  have ht:=hsR.mul_left ((H 0 z).re^h)
  have hH:(H 0 z).re≠0:=(H_zero_re_pos z hz).ne'
  have he:(H 0 z).re^h*((H 0 z).re⁻¹^h)=1:=by rw[←mul_pow,mul_inv_cancel₀ hH,one_pow]
  rw[he] at ht
  convert ht using 1
  funext m
  rw[tiltedKernelMass_eq_unscaled]
  ring
lemma tiltedKernelMass_le_one (z:ℝ)(hz:z∈Icc (0:ℝ) (r 0))(h m:ℕ)(hh:0<h):
    tiltedKernelMass z h m≤1:=by
  have hs:=tiltedKernelMass_hasSum z hz h
  have hl:=hs.summable.le_tsum m (fun n _=>tiltedKernelMass_nonneg z hz h n hh)
  rwa[hs.tsum_eq] at hl
end WP.Coefficients
