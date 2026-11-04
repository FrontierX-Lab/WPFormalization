import WPFormalization.Analysis.GevreyTwoSequence
/-! Actual Gevrey-two polynomial product errors on the quadratic Cauchy
scale. These estimates propagate true errors using the existing formal
product coefficients. -/
noncomputable section
namespace WP.Analysis
open PowerSeries
lemma complex_taylor_quadratic_factorial_bound (f:ℂ→ℂ) (B M:ℝ) (hB:0<B) (hM:0≤M)
    (K:ℕ) (hd:DifferentiableOn ℂ f (Metric.closedBall 0 (1/(2*B*((K:ℝ)+1)^2))))
    (hc:∀z∈Metric.sphere (0:ℂ) (1/(2*B*((K:ℝ)+1)^2)),‖f z‖≤M)
    (z:ℂ) (hz:‖z‖≤1/(4*B*((K:ℝ)+1)^2)):
    ‖f z-∑i∈Finset.range (K+1),WP.coeff f i*z^i‖≤
      2*M*(2*B*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2*‖z‖^(K+1):=by
  let R:ℝ:=1/(2*B*((K:ℝ)+1)^2)
  have hR:0<R:=by dsimp[R];positivity
  have hzR:‖z‖≤R/2:=by convert hz using 1;dsimp[R];field_simp;ring
  have he:=complex_taylor_remainder_bound f R M hR hM hd hc (K+1) z hzR
  apply he.trans
  have hratio:‖z‖/R=(2*B*‖z‖)*((K+1:ℕ):ℝ)^2:=by dsimp[R];push_cast;field_simp
  have hp:((((K+1:ℕ):ℝ)^2)^(K+1))=((((K+1:ℕ):ℝ)^(K+1))^2):=by
    rw[←pow_mul,←pow_mul];congr 1;omega
  rw[hratio,mul_pow,hp]
  have hfac:=pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg (K+1)) (K+1))
    (order_pow_le_exp_factorial (K+1)) 2
  calc
    _≤2*M*((2*B*‖z‖)^(K+1)*(((Real.exp 1)^(K+1)*((K+1).factorial:ℝ))^2)):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac (by positivity)) (by positivity)
    _=_:=by
      have hpow:((Real.exp 1)^2)^(K+1)=((Real.exp 1)^(K+1))^2:=by
        rw[←pow_mul,←pow_mul];congr 1;omega
      simp only[mul_pow,hpow];ring

lemma truncatedSeriesPolynomial_gevreyTwo_mul_remainder (f g:WP.HigherOrder.Series) (C B:ℝ)
    (hC:0≤C) (hB:0<B)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ)^2)
    (hg:∀n,|PowerSeries.coeff n g|≤C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ) (z:ℂ) (hz:‖z‖≤1/(4*B*((K:ℝ)+1)^2)) :
    ‖truncatedSeriesPolynomial f K z*truncatedSeriesPolynomial g K z-
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (f*g):ℝ):ℂ)*z^i‖≤
      8*C^2*(2*B*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2*‖z‖^(K+1) := by
  have hd:DifferentiableOn ℂ (fun w=>truncatedSeriesPolynomial f K w*truncatedSeriesPolynomial g K w)
      (Metric.closedBall 0 (1/(2*B*((K:ℝ)+1)^2))) := by
    intro w hw
    exact ((truncatedSeriesPolynomial_analytic f K w).mul
      (truncatedSeriesPolynomial_analytic g K w)).differentiableAt.differentiableWithinAt
  have hc:∀w∈Metric.sphere (0:ℂ) (1/(2*B*((K:ℝ)+1)^2)),
      ‖truncatedSeriesPolynomial f K w*truncatedSeriesPolynomial g K w‖≤4*C^2 := by
    intro w hw
    have hwR:‖w‖≤1/(2*B*((K:ℝ)+1)^2) := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using Metric.sphere_subset_closedBall hw
    rw [norm_mul]
    have he:=mul_le_mul (truncatedSeriesPolynomial_gevreyTwo_norm_bound f C B hC hB hf K w hwR)
      (truncatedSeriesPolynomial_gevreyTwo_norm_bound g C B hC hB hg K w hwR) (norm_nonneg _) (by positivity)
    nlinarith
  have he:=complex_taylor_quadratic_factorial_bound
    (fun w=>truncatedSeriesPolynomial f K w*truncatedSeriesPolynomial g K w) B (4*C^2) hB
    (by positivity) K hd hc z hz
  have hcoef:(∑i∈Finset.range (K+1),WP.coeff
      (fun w=>truncatedSeriesPolynomial f K w*truncatedSeriesPolynomial g K w) i*z^i)=
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (f*g):ℝ):ℂ)*z^i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [truncatedSeriesPolynomial_mul_coeff f g K i (by have := Finset.mem_range.mp hi;omega)]
  rw [hcoef] at he
  convert he using 1;ring

lemma truncatedSeriesPolynomial_gevreyTwo_mul_real_remainder (f g:WP.HigherOrder.Series) (C B:ℝ)
    (hC:0≤C) (hB:0<B)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ)^2)
    (hg:∀n,|PowerSeries.coeff n g|≤C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ) (h:ℝ) (hh:0<h) (hwindow:4*B*((K:ℝ)+1)^2≤h) :
    |inversePowerTruncation f K h*inversePowerTruncation g K h-inversePowerTruncation (f*g) K h|≤
      8*C^2*(2*B*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1) := by
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(4*B*((K:ℝ)+1)^2) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
    exact one_div_le_one_div_of_le (by positivity) hwindow
  have he:=truncatedSeriesPolynomial_gevreyTwo_mul_remainder f g C B hC hB hf hg K ((1/h:ℝ):ℂ) hz
  have hp (s:WP.HigherOrder.Series):truncatedSeriesPolynomial s K ((1/h:ℝ):ℂ)=
      ((inversePowerTruncation s K h):ℂ) := by
    rw [truncatedSeriesPolynomial_real]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow,one_pow,mul_one_div]
  have hq:(∑i∈Finset.range (K+1),((PowerSeries.coeff i (f*g):ℝ):ℂ)*((1/h:ℝ):ℂ)^i)=
      ((inversePowerTruncation (f*g) K h):ℂ) := by
    change truncatedSeriesPolynomial (f*g) K ((1/h:ℝ):ℂ)=_
    exact hp (f*g)
  rw [hp,hp,hq,←Complex.ofReal_mul,←Complex.ofReal_sub] at he
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh),div_pow,one_pow] at he
  convert he using 1;ring

lemma inversePowerTruncation_gevreyTwo_abs_bound (f:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ)(h:ℝ)(hh:0<h)(hw:2*B*((K:ℝ)+1)^2≤h):
    |inversePowerTruncation f K h|≤2*C:=by
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(2*B*((K:ℝ)+1)^2):=by
    rw[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
    exact one_div_le_one_div_of_le (by positivity) hw
  have he:=truncatedSeriesPolynomial_gevreyTwo_norm_bound f C B hC hB hf K ((1/h:ℝ):ℂ) hz
  rw[truncatedSeriesPolynomial_real,Complex.norm_real,Real.norm_eq_abs] at he
  convert he using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw[div_pow,one_pow,mul_one_div]

lemma mul_value_gevreyTwo_truncation_error (f g:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ)^2)
    (hg:∀n,|PowerSeries.coeff n g|≤C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ)(h:ℝ)(hh:0<h)(hw:4*B*((K:ℝ)+1)^2≤h)
    (x y E F M:ℝ)(hx:|x-inversePowerTruncation f K h|≤E)
    (hy:|y-inversePowerTruncation g K h|≤F)(hyM:|y|≤M):
    |x*y-inversePowerTruncation (f*g) K h|≤M*E+2*C*F+
      8*C^2*(2*B*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
  have hE:0≤E:=(abs_nonneg _).trans hx
  have hF:0≤F:=(abs_nonneg _).trans hy
  have hP:|inversePowerTruncation f K h|≤2*C:=
    inversePowerTruncation_gevreyTwo_abs_bound f C B hC hB hf K h hh (by nlinarith[Nat.cast_nonneg (α:=ℝ) K])
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
    (truncatedSeriesPolynomial_gevreyTwo_mul_real_remainder f g C B hC hB hf hg K h hh hw))


end WP.Analysis
