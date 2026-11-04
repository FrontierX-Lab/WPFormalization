import WPFormalization.Analysis.UniformTaylorRemainder
/-! Cauchy bounds and the local Gaussian error of a genuine analytic
log action and amplitude. Exact quadratic jets identify the Gaussian;
the cubic remainder and amplitude variation give the explicit error. -/
noncomputable section
namespace WP.Analysis
open Set Complex

lemma analytic_value_sub_zero_norm_bound (f:ℂ→ℂ)(R M:ℝ)(hR:0<R)(hM:0≤M)
    (hf:DifferentiableOn ℂ f (Metric.closedBall 0 R))
    (hb:∀z∈Metric.sphere (0:ℂ) R,‖f z‖≤M)(z:ℂ)(hz:‖z‖≤R/2):
    ‖f z-f 0‖≤(2*M/R)*‖z‖:=by
  have he:=complex_taylor_remainder_bound f R M hR hM hf hb 1 z hz
  have ht:‖f z-f 0‖≤2*M*(‖z‖/R):=by simpa [Finset.sum_range_succ,WP.coeff] using he
  convert ht using 1 <;>ring

lemma gaussian_pointwise_error_of_log_amplitude (L A:ℂ)(t η ε D:ℝ)
    (hL:‖L-((-(t^2)/2:ℝ):ℂ)‖≤η)(hη:η≤1)
    (hA:‖A‖≤D)(hA1:‖A-1‖≤ε):
    ‖Complex.exp L*A-Complex.exp (((-(t^2)/2:ℝ):ℂ))‖≤
      Real.exp (-t^2/2)*(2*η*D+ε):=by
  let q:ℂ:=((-(t^2)/2:ℝ):ℂ)
  let E:ℂ:=L-q
  have hE:‖E‖≤1:=hL.trans hη
  have hEn:‖Complex.exp E-1‖≤2*η:=(Complex.norm_exp_sub_one_le hE).trans (by linarith[hL])
  have he:Complex.exp L*A-Complex.exp q=
      Complex.exp q*((Complex.exp E-1)*A+(A-1)):=by
    have hEL:q+E=L:=by dsimp[E];ring
    rw[show Complex.exp L=Complex.exp q*Complex.exp E by rw[←Complex.exp_add,hEL]]
    ring
  have hD:0≤D:=(norm_nonneg A).trans hA
  rw[he,norm_mul,Complex.norm_exp]
  change Real.exp (-t^2/2)*_≤_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    ‖(Complex.exp E-1)*A+(A-1)‖≤‖(Complex.exp E-1)*A‖+‖A-1‖:=norm_add_le _ _
    _≤2*η*D+ε:=by
      rw[norm_mul]
      exact add_le_add (mul_le_mul hEn hA (norm_nonneg A) (by linarith[norm_nonneg E,hL])) hA1


lemma gaussian_characteristic_local_bound (L A:ℂ→ℂ)(R M D:ℝ)
    (hR:0<R)(hM:0≤M)(hD:0≤D)
    (hL:DifferentiableOn ℂ L (Metric.closedBall 0 R))
    (hA:DifferentiableOn ℂ A (Metric.closedBall 0 R))
    (hbL:∀z∈Metric.sphere (0:ℂ) R,‖L z‖≤M)
    (hbA:∀z∈Metric.sphere (0:ℂ) R,‖A z‖≤D)
    (hc0:WP.coeff L 0=0)(hc1:WP.coeff L 1=0)(hc2:WP.coeff L 2=(1/2:ℂ))
    (hA0:A 0=1)(t:ℝ)(ht:|t|≤R/2)
    (hsmall:(2*M/R^3)*|t|^3≤1)
    (hAt:‖A ((t:ℂ)*Complex.I)‖≤D):
    ‖Complex.exp (L ((t:ℂ)*Complex.I))*A ((t:ℂ)*Complex.I)-
      Complex.exp (((-t^2/2:ℝ):ℂ))‖≤
        Real.exp (-t^2/2)*(4*M*D/R^3*|t|^3+2*D/R*|t|):=by
  have hn:‖(t:ℂ)*Complex.I‖=|t|:=by rw[norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hz:‖(t:ℂ)*Complex.I‖≤R/2:=by rwa[hn]
  have he:=complex_quadratic_remainder_bound L R M hR hM hL hbL ((t:ℂ)*Complex.I) hz
  have hp:(1/2:ℂ)*((t:ℂ)*Complex.I)^2=((-(t^2)/2:ℝ):ℂ):=by
    rw[mul_pow,Complex.I_sq]
    push_cast
    ring
  rw[hc0,hc1,hc2,zero_mul,zero_add,zero_add,hp,hn] at he
  have ha:=analytic_value_sub_zero_norm_bound A R D hR hD hA hbA ((t:ℂ)*Complex.I) hz
  rw[hA0,hn] at ha
  have ho:=gaussian_pointwise_error_of_log_amplitude _ _ t _ _ D he hsmall hAt ha
  convert ho using 1 <;>ring
end WP.Analysis
