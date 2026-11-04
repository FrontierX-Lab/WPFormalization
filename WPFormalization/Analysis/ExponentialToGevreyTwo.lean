import WPFormalization.Analysis.FiniteWatson
import WPFormalization.Analysis.FactorialKernelMoments
/-! A genuine exp(-a sqrt(h)) tail is bounded at every Gevrey-two order by an explicit factorial estimate. -/
noncomputable section
namespace WP.Analysis
lemma exp_neg_sqrt_gevrey_two_bound (a h:ℝ) (ha:0<a) (hh:0<h) (N:ℕ) :
    Real.exp (-a*Real.sqrt h)≤(4/a^2)^N*(N.factorial:ℝ)^2/h^N := by
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have he:=exp_neg_factorial_bound a (Real.sqrt h) ha hs (2*N)
  have hpow:(Real.sqrt h)^(2*N)=h^N:=by rw[pow_mul,Real.sq_sqrt hh.le]
  rw[hpow] at he
  rw[show -a*Real.sqrt h=-(a*Real.sqrt h) by ring]
  apply he.trans
  calc _ ≤ a⁻¹^(2*N)*((4:ℝ)^N*(N.factorial:ℝ)^2)/h^N :=
             div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (factorial_double_le_four_pow N) (by positivity)) (pow_nonneg hh.le _)
       _ = _:=by simp only[pow_mul,div_pow,mul_pow,inv_pow];ring
end WP.Analysis
