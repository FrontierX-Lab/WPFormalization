import WPFormalization.Analysis.FiniteExpGevrey
/-! Uniform finite exponential bounds for Gevrey-two jets.
A radius proportional to (K+1)^(-2) gives the square-factorial Cauchy tail.
The actual exponential error has explicit constants and uses the genuine finiteExp coefficients. -/

noncomputable section
namespace WP.Analysis
open PowerSeries Filter
open scoped Topology
lemma factorial_sq_le_order_pow (n K:ℕ) (hn:n ≤ K) :
    (n.factorial:ℝ)^2 ≤ (((K:ℝ)+1)^2)^n:=by
  calc
    _ ≤ (((K:ℝ)+1)^n)^2:=pow_le_pow_left₀ (Nat.cast_nonneg _) (factorial_le_order_pow n K hn) 2
    _=_:=by rw[←pow_mul,←pow_mul];congr 1;omega

lemma truncatedSeriesPolynomial_gevreyTwo_norm_bound (f:WP.HigherOrder.Series) (C B:ℝ)
    (hC:0 ≤ C) (hB:0<B) (hf:∀n,|PowerSeries.coeff n f| ≤ C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ) (z:ℂ) (hz:‖z‖ ≤ 1/(2*B*((K:ℝ)+1)^2)) :
    ‖truncatedSeriesPolynomial f K z‖ ≤ 2*C:=by
  have ht (n:ℕ) (hn:n∈Finset.range (K+1)) :
      ‖((PowerSeries.coeff n f:ℝ):ℂ)*z^n‖ ≤ C*(1/(2:ℝ))^n:=by
    have hnK:n ≤ K:=by have hh:=Finset.mem_range.mp hn;omega
    rw[norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (C*B^n*(n.factorial:ℝ)^2)*(1/(2*B*((K:ℝ)+1)^2))^n:=
        mul_le_mul (hf n) (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity) (by positivity)
      _ ≤ (C*B^n*(((K:ℝ)+1)^2)^n)*(1/(2*B*((K:ℝ)+1)^2))^n:=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (factorial_sq_le_order_pow n K hnK) (by positivity)) (by positivity)
      _=_:=by
        have he:B*((K:ℝ)+1)^2*(1/(2*B*((K:ℝ)+1)^2))=1/(2:ℝ):=by field_simp
        calc
          _=C*(B*((K:ℝ)+1)^2*(1/(2*B*((K:ℝ)+1)^2)))^n:=by simp only[mul_pow];ring
          _=_:=by rw[he]
  unfold truncatedSeriesPolynomial
  calc
    _ ≤ ∑n∈Finset.range (K+1),‖((PowerSeries.coeff n f:ℝ):ℂ)*z^n‖:=norm_sum_le _ _
    _ ≤ ∑n∈Finset.range (K+1),C*(1/(2:ℝ))^n:=Finset.sum_le_sum ht
    _=C*(∑n∈Finset.range (K+1),(1/(2:ℝ))^n):=(Finset.mul_sum _ _ _).symm
    _ ≤ C*2:=mul_le_mul_of_nonneg_left (sum_geometric_two_le _) hC
    _=2*C:=by ring

lemma finiteExp_gevreyTwo_truncated_polynomial_remainder (f:WP.HigherOrder.Series) (C B:ℝ)
    (hC:0 ≤ C) (hB:0<B) (hf0:PowerSeries.constantCoeff f=0)
    (hf:∀n,|PowerSeries.coeff n f| ≤ C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ) (z:ℂ) (hz:‖z‖ ≤ 1/(4*B*((K:ℝ)+1)^2)) :
    ‖Complex.exp (truncatedSeriesPolynomial f K z)-
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.finiteExp f):ℝ):ℂ)*z^i‖ ≤
      2*Real.exp (2*C)*(2*B*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2*‖z‖^(K+1):=by
  let R:ℝ:=1/(2*B*((K:ℝ)+1)^2)
  have hR:0<R:=by dsimp[R];positivity
  have hfun:DifferentiableOn ℂ (fun w=>Complex.exp (truncatedSeriesPolynomial f K w))
      (Metric.closedBall 0 R):=by
    intro w hw
    exact ((Complex.hasDerivAt_exp _).comp w (truncatedSeriesPolynomial_analytic f K w).differentiableAt.hasDerivAt).differentiableAt.differentiableWithinAt
  have hcircle:∀w∈Metric.sphere (0:ℂ) R,‖Complex.exp (truncatedSeriesPolynomial f K w)‖ ≤ Real.exp (2*C):=by
    intro w hw
    have hwR:‖w‖ ≤ R:=by simpa only[Metric.mem_closedBall,dist_zero_right] using Metric.sphere_subset_closedBall hw
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr
      (truncatedSeriesPolynomial_gevreyTwo_norm_bound f C B hC hB hf K w hwR))
  have hzR:‖z‖ ≤ R/2:=by
    have he:R/2=1/(4*B*((K:ℝ)+1)^2):=by dsimp[R];field_simp;ring
    rwa[he]
  have he:=complex_taylor_remainder_bound (fun w=>Complex.exp (truncatedSeriesPolynomial f K w))
    R (Real.exp (2*C)) hR (Real.exp_pos _).le hfun hcircle (K+1) z hzR
  have hcoef:(∑i∈Finset.range (K+1),WP.coeff (fun w=>Complex.exp (truncatedSeriesPolynomial f K w)) i*z^i)=
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.finiteExp f):ℝ):ℂ)*z^i:=by
    apply Finset.sum_congr rfl
    intro i hi
    rw[finiteExp_truncated_polynomial_coeff f hf0 K i (by have hh:=Finset.mem_range.mp hi;omega)]
  rw[hcoef] at he
  apply he.trans
  have hratio:‖z‖/R=(2*B*‖z‖)*((K+1:ℕ):ℝ)^2:=by
    dsimp[R]
    push_cast
    field_simp
  have hp:((((K+1:ℕ):ℝ)^2)^(K+1))=((((K+1:ℕ):ℝ)^(K+1))^2):=by
    rw[←pow_mul,←pow_mul];congr 1;omega
  rw[hratio,mul_pow,hp]
  have hfac:=pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg (K+1)) (K+1))
    (order_pow_le_exp_factorial (K+1)) 2
  calc
    _ ≤ 2*Real.exp (2*C)*((2*B*‖z‖)^(K+1)*(((Real.exp 1)^(K+1)*((K+1).factorial:ℝ))^2)):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac (by positivity)) (by positivity)
    _=_:=by
      have hpow:((Real.exp 1)^2)^(K+1)=((Real.exp 1)^(K+1))^2:=by
        rw[←pow_mul,←pow_mul];congr 1;omega
      simp only[mul_pow,hpow]
      ring

lemma finiteExp_gevreyTwo_real_polynomial_remainder (f:WP.HigherOrder.Series) (C B:ℝ)
    (hC:0≤C) (hB:0<B) (hf0:PowerSeries.constantCoeff f=0)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ) (h:ℝ) (hh:0<h) (hwindow:4*B*((K:ℝ)+1)^2≤h) :
    |Real.exp (∑i∈Finset.range (K+1),PowerSeries.coeff i f/h^i)-
      ∑i∈Finset.range (K+1),PowerSeries.coeff i (WP.HigherOrder.finiteExp f)/h^i|≤
      2*Real.exp (2*C)*(2*B*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1) := by
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(4*B*((K:ℝ)+1)^2) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) hwindow
  have he := finiteExp_gevreyTwo_truncated_polynomial_remainder f C B hC hB hf0 hf K ((1/h:ℝ):ℂ) hz
  rw [truncatedSeriesPolynomial_real] at he
  have hp (g:WP.HigherOrder.Series):
      (∑i∈Finset.range (K+1),((PowerSeries.coeff i g:ℝ):ℂ)*((1/h:ℝ):ℂ)^i)=
        ((∑i∈Finset.range (K+1),PowerSeries.coeff i g/h^i:ℝ):ℂ) := by
    simp only [Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_one,div_pow,one_pow]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hpR:(∑i∈Finset.range (K+1),PowerSeries.coeff i f*(1/h)^i)=
      ∑i∈Finset.range (K+1),PowerSeries.coeff i f/h^i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow,one_pow,mul_one_div]
  rw [hpR,hp,←Complex.ofReal_exp,←Complex.ofReal_sub] at he
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh),div_pow,one_pow] at he
  convert he using 1;ring


lemma inverse_truncated_polynomial_gevreyTwo_abs_bound (f:WP.HigherOrder.Series) (C B:ℝ)
    (hC:0 ≤ C) (hB:0<B) (hf:∀n,|PowerSeries.coeff n f| ≤ C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ) (h:ℝ) (hh:0<h) (hwindow:2*B*((K:ℝ)+1)^2 ≤ h) :
    |∑i∈Finset.range (K+1),PowerSeries.coeff i f/h^i| ≤ 2*C:=by
  have hz:‖((1/h:ℝ):ℂ)‖ ≤ 1/(2*B*((K:ℝ)+1)^2):=by
    rw[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
    exact one_div_le_one_div_of_le (by positivity) hwindow
  have hp:=truncatedSeriesPolynomial_gevreyTwo_norm_bound f C B hC hB hf K ((1/h:ℝ):ℂ) hz
  rw[truncatedSeriesPolynomial_real] at hp
  have he:(∑i∈Finset.range (K+1),PowerSeries.coeff i f*(1/h)^i)=
      ∑i∈Finset.range (K+1),PowerSeries.coeff i f/h^i:=by
    apply Finset.sum_congr rfl
    intro i hi
    rw[div_pow,one_pow,mul_one_div]
  rw[he] at hp
  simpa only[Complex.norm_real,Real.norm_eq_abs] using hp

lemma finiteExp_gevreyTwo_error_of_log_error (f:WP.HigherOrder.Series) (C B C₀ B₀ M:ℝ)
    (hC:0 ≤ C) (hB:0<B) (hC₀:0 ≤ C₀) (hB₀:0 ≤ B₀) (hM:2*C ≤ M)
    (hf0:PowerSeries.constantCoeff f=0)
    (hf:∀n,|PowerSeries.coeff n f| ≤ C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ) (h x:ℝ) (hh:0<h) (hwindow:4*B*((K:ℝ)+1)^2 ≤ h) (hx:x ≤ M)
    (herr:|x-∑i∈Finset.range (K+1),PowerSeries.coeff i f/h^i| ≤
      C₀*B₀^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)) :
    |Real.exp x-∑i∈Finset.range (K+1),PowerSeries.coeff i (WP.HigherOrder.finiteExp f)/h^i| ≤
      (Real.exp M*C₀+2*Real.exp (2*C))*(B₀+2*B*(Real.exp 1)^2)^(K+1)*
        ((K+1).factorial:ℝ)^2/h^(K+1):=by
  have hpoly: (∑i∈Finset.range (K+1),PowerSeries.coeff i f/h^i) ≤ M:=
    (le_abs_self _).trans ((inverse_truncated_polynomial_gevreyTwo_abs_bound f C B hC hB hf K h hh
      (by nlinarith[sq_nonneg ((K:ℝ)+1)])).trans hM)
  have hexp:=exp_abs_sub_le M x _ hx hpoly
  have ht:=finiteExp_gevreyTwo_real_polynomial_remainder f C B hC hB hf0 hf K h hh hwindow
  have hp₀:B₀^(K+1) ≤ (B₀+2*B*(Real.exp 1)^2)^(K+1):=
    pow_le_pow_left₀ hB₀ (by nlinarith[Real.exp_pos 1,sq_pos_of_pos (Real.exp_pos 1)]) _
  have hp₁:(2*B*(Real.exp 1)^2)^(K+1) ≤ (B₀+2*B*(Real.exp 1)^2)^(K+1):=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hb:=add_le_add (mul_le_mul_of_nonneg_left hp₀ (by positivity:0 ≤ Real.exp M*C₀))
    (mul_le_mul_of_nonneg_left hp₁ (by positivity:0 ≤ 2*Real.exp (2*C)))
  have hb':=mul_le_mul_of_nonneg_right hb (show 0 ≤ ((K+1).factorial:ℝ)^2/h^(K+1) by positivity)
  calc
    _ ≤ |Real.exp x-Real.exp (∑i∈Finset.range (K+1),PowerSeries.coeff i f/h^i)|+
      |Real.exp (∑i∈Finset.range (K+1),PowerSeries.coeff i f/h^i)-
        ∑i∈Finset.range (K+1),PowerSeries.coeff i (WP.HigherOrder.finiteExp f)/h^i|:=abs_sub_le _ _ _
    _ ≤ Real.exp M*(C₀*B₀^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))+
      2*Real.exp (2*C)*(2*B*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=
      add_le_add (hexp.trans (mul_le_mul_of_nonneg_left herr (Real.exp_pos _).le)) ht
    _ ≤ _:=by convert hb' using 1 <;>ring

end WP.Analysis
