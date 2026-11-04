import WPFormalization.Analysis.GevreyTwoPointwise
/-! True complex source errors multiply by real Gevrey-two expansions through the original formal product coefficients; no reality of the complex source is assumed. -/
noncomputable section
namespace WP.Analysis
lemma complex_mul_real_approximation_error (x:ℂ) (y p q t E F G C M:ℝ)
    (hx:‖x-(p:ℂ)‖≤E) (hy:|y-q|≤F) (hp:|p|≤C) (hyM:|y|≤M)
    (ht:|p*q-t|≤G) :
    ‖x*(y:ℂ)-(t:ℂ)‖≤M*E+C*F+G := by
  have hE:0≤E:=(norm_nonneg _).trans hx
  have hF:0≤F:=(abs_nonneg _).trans hy
  have hC:0≤C:=(abs_nonneg _).trans hp
  have he:x*(y:ℂ)-(t:ℂ)=(x-(p:ℂ))*(y:ℂ)+(p:ℂ)*((y-q:ℝ):ℂ)+((p*q-t:ℝ):ℂ) := by
    push_cast
    ring
  rw[he]
  have hn:‖x-(p:ℂ)‖*|y|≤E*M:=mul_le_mul hx hyM (abs_nonneg _) hE
  have hm:|p| * |y-q|≤C*F:=mul_le_mul hp hy (abs_nonneg _) hC
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only[norm_mul,Complex.norm_real,Real.norm_eq_abs]
  nlinarith
end WP.Analysis

namespace WP.Analysis
lemma complex_mul_value_gevreyTwo_truncation_error (f g:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ)^2)
    (hg:∀n,|PowerSeries.coeff n g|≤C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ)(h:ℝ)(hh:0<h)(hw:4*B*((K:ℝ)+1)^2≤h)
    (x:ℂ) (y E F M:ℝ)(hx:‖x-(inversePowerTruncation f K h:ℂ)‖≤E)
    (hy:|y-inversePowerTruncation g K h|≤F)(hyM:|y|≤M):
    ‖x*(y:ℂ)-(inversePowerTruncation (f*g) K h:ℂ)‖≤M*E+2*C*F+
      8*C^2*(2*B*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
  have hP:|inversePowerTruncation f K h|≤2*C:=
    inversePowerTruncation_gevreyTwo_abs_bound f C B hC hB hf K h hh (by nlinarith[Nat.cast_nonneg (α:=ℝ) K])
  exact complex_mul_real_approximation_error x y (inversePowerTruncation f K h)
    (inversePowerTruncation g K h) (inversePowerTruncation (f*g) K h) E F
    (8*C^2*(2*B*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)) (2*C) M hx hy hP hyM
    (truncatedSeriesPolynomial_gevreyTwo_mul_real_remainder f g C B hC hB hf hg K h hh hw)
end WP.Analysis
