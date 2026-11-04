import WPFormalization.Analysis.GevreyOneMatching
/-! Pointwise actual-value error propagation, usable at arbitrary real scales
including scales sampled only along a discrete genus sequence. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open PowerSeries

lemma inversePowerTruncation_abs_bound (f:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(h:ℝ)(hh:0<h)(hw:2*B*((K:ℝ)+1)≤h):
    |inversePowerTruncation f K h|≤2*C:=by
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(2*B*((K:ℝ)+1)):=by
    rw[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
    exact one_div_le_one_div_of_le (by positivity) hw
  have he:=truncatedSeriesPolynomial_norm_bound f C B hC hB hf K ((1/h:ℝ):ℂ) hz
  rw[truncatedSeriesPolynomial_real,Complex.norm_real,Real.norm_eq_abs] at he
  convert he using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw[div_pow,one_pow,mul_one_div]

lemma mul_value_truncation_error (f g:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (hg:∀n,|PowerSeries.coeff n g|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(h:ℝ)(hh:0<h)(hw:4*B*((K:ℝ)+1)≤h)
    (x y E F M:ℝ)(hx:|x-inversePowerTruncation f K h|≤E)
    (hy:|y-inversePowerTruncation g K h|≤F)(hyM:|y|≤M):
    |x*y-inversePowerTruncation (f*g) K h|≤M*E+2*C*F+
      8*C^2*(2*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
  have hE:0≤E:=(abs_nonneg _).trans hx
  have hF:0≤F:=(abs_nonneg _).trans hy
  have hP:|inversePowerTruncation f K h|≤2*C:=
    inversePowerTruncation_abs_bound f C B hC hB hf K h hh (by nlinarith[Nat.cast_nonneg (α:=ℝ) K])
  have hprod:|x*y-inversePowerTruncation f K h*inversePowerTruncation g K h|≤M*E+2*C*F:=by
    have he:x*y-inversePowerTruncation f K h*inversePowerTruncation g K h=
        (x-inversePowerTruncation f K h)*y+
          inversePowerTruncation f K h*(y-inversePowerTruncation g K h):=by ring
    rw[he]
    apply (abs_add_le _ _).trans
    simp only[abs_mul]
    have h₁:=mul_le_mul hx hyM (abs_nonneg _) hE
    have h₂:=mul_le_mul hP hy (abs_nonneg _) (mul_nonneg (by norm_num) hC)
    nlinarith
  exact (abs_sub_le _ _ _).trans (add_le_add hprod
    (truncatedSeriesPolynomial_mul_real_remainder f g C B hC hB hf hg K h hh hw))

end WP.Analysis
