import WPFormalization.Analysis.FiniteExpTaylor
import WPFormalization.Analysis.UniformTaylorRemainder
/-! Uniform factorial Taylor errors for exponentials of finite Gevrey-one polynomials. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open PowerSeries Filter
open scoped Topology

lemma factorial_le_order_pow (n K : ℕ) (hn : n≤K) :
    (n.factorial:ℝ)≤((K:ℝ)+1)^n := by
  have hnK : n≤K+1 := by omega
  have hh := (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left hnK n)
  exact_mod_cast hh

lemma truncatedSeriesPolynomial_norm_bound (f : WP.HigherOrder.Series) (C B : ℝ)
    (hC : 0≤C) (hB : 0<B)
    (hf : ∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K : ℕ) (z : ℂ) (hz : ‖z‖≤1/(2*B*((K:ℝ)+1))) :
    ‖truncatedSeriesPolynomial f K z‖≤2*C := by
  have hK : 0<(K:ℝ)+1 := by positivity
  have hR : 0<1/(2*B*((K:ℝ)+1)) := by positivity
  have ht (n : ℕ) (hn : n∈Finset.range (K+1)) :
      ‖((PowerSeries.coeff n f:ℝ):ℂ)*z^n‖≤C*(1/(2:ℝ))^n := by
    have hnK : n≤K := by have := Finset.mem_range.mp hn;omega
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (C*B^n*(n.factorial:ℝ))*(1/(2*B*((K:ℝ)+1)))^n :=
        mul_le_mul (hf n) (pow_le_pow_left₀ (norm_nonneg _) hz n)
          (pow_nonneg (norm_nonneg _) n) (by positivity)
      _ ≤ (C*B^n*((K:ℝ)+1)^n)*(1/(2*B*((K:ℝ)+1)))^n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (factorial_le_order_pow n K hnK) (mul_nonneg hC (pow_nonneg hB.le n))) (by positivity)
      _ = _ := by
        have he : B*((K:ℝ)+1)*(1/(2*B*((K:ℝ)+1)))=1/(2:ℝ) := by field_simp
        calc
          _ = C*(B*((K:ℝ)+1)*(1/(2*B*((K:ℝ)+1))))^n := by simp only [mul_pow];ring
          _ = _ := by rw [he]
  unfold truncatedSeriesPolynomial
  calc
    _ ≤ ∑n∈Finset.range (K+1),‖((PowerSeries.coeff n f:ℝ):ℂ)*z^n‖ := norm_sum_le _ _
    _ ≤ ∑n∈Finset.range (K+1),C*(1/(2:ℝ))^n := Finset.sum_le_sum ht
    _ = C*(∑n∈Finset.range (K+1),(1/(2:ℝ))^n) := (Finset.mul_sum _ _ _).symm
    _ ≤ C*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le (K+1)) hC
    _ = _ := by ring


lemma order_pow_le_exp_factorial (N : ℕ) :
    (N:ℝ)^N≤(Real.exp 1)^N*(N.factorial:ℝ) := by
  have hF : 0<(N.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos N
  have he := (div_le_iff₀ hF).mp (Real.pow_div_factorial_le_exp (N:ℝ) (Nat.cast_nonneg N) N)
  simpa only [←Real.exp_nat_mul,mul_one] using he

lemma finiteExp_truncated_polynomial_remainder (f : WP.HigherOrder.Series) (C B : ℝ)
    (hC : 0≤C) (hB : 0<B) (hf0 : PowerSeries.constantCoeff f=0)
    (hf : ∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K : ℕ) (z : ℂ) (hz : ‖z‖≤1/(4*B*((K:ℝ)+1))) :
    ‖Complex.exp (truncatedSeriesPolynomial f K z)-
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.finiteExp f):ℝ):ℂ)*z^i‖≤
      2*Real.exp (2*C)*(2*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)*‖z‖^(K+1) := by
  let R : ℝ := 1/(2*B*((K:ℝ)+1))
  have hR : 0<R := by dsimp only [R];positivity
  have hfun : DifferentiableOn ℂ (fun w=>Complex.exp (truncatedSeriesPolynomial f K w))
      (Metric.closedBall 0 R) := by
    intro w hw
    exact ((Complex.hasDerivAt_exp _).comp w (truncatedSeriesPolynomial_analytic f K w).differentiableAt.hasDerivAt).differentiableAt.differentiableWithinAt
  have hcircle : ∀w∈Metric.sphere (0:ℂ) R,
      ‖Complex.exp (truncatedSeriesPolynomial f K w)‖≤Real.exp (2*C) := by
    intro w hw
    have hwR : ‖w‖≤R := by simpa only [Metric.mem_closedBall,dist_zero_right] using Metric.sphere_subset_closedBall hw
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr
      (truncatedSeriesPolynomial_norm_bound f C B hC hB hf K w hwR))
  have hzR : ‖z‖≤R/2 := by
    have he : R/2=1/(4*B*((K:ℝ)+1)) := by dsimp only [R];field_simp;ring
    rwa [he]
  have he := complex_taylor_remainder_bound (fun w=>Complex.exp (truncatedSeriesPolynomial f K w))
    R (Real.exp (2*C)) hR (Real.exp_pos _).le hfun hcircle (K+1) z hzR
  have hcoef : (∑i∈Finset.range (K+1),WP.coeff (fun w=>Complex.exp (truncatedSeriesPolynomial f K w)) i*z^i)=
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.finiteExp f):ℝ):ℂ)*z^i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [finiteExp_truncated_polynomial_coeff f hf0 K i (by have := Finset.mem_range.mp hi;omega)]
  rw [hcoef] at he
  apply he.trans
  have hratio : ‖z‖/R=(2*B*‖z‖)*((K+1:ℕ):ℝ) := by
    dsimp only [R]
    push_cast
    field_simp
  rw [hratio,mul_pow]
  calc
    _ ≤ 2*Real.exp (2*C)*((2*B*‖z‖)^(K+1)*((Real.exp 1)^(K+1)*((K+1).factorial:ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (order_pow_le_exp_factorial (K+1))
        (pow_nonneg (by positivity) _)) (by positivity)
    _ = _ := by simp only [mul_pow];ring


lemma exp_abs_sub_le (M x y : ℝ) (hx : x≤M) (hy : y≤M) :
    |Real.exp x-Real.exp y|≤Real.exp M*|x-y| := by
  have hb : ∀t∈Set.Iic M,‖deriv Real.exp t‖≤Real.exp M := by
    intro t ht
    rw [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ht
  have he := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_:t∈Set.Iic M)=>Real.differentiableAt_exp) hb (convex_Iic M) (show y∈Set.Iic M from hy) (show x∈Set.Iic M from hx)
  simpa only [Real.norm_eq_abs] using he


lemma truncatedSeriesPolynomial_real (f:WP.HigherOrder.Series) (K:ℕ) (x:ℝ) :
    truncatedSeriesPolynomial f K (x:ℂ)=((∑i∈Finset.range (K+1),PowerSeries.coeff i f*x^i:ℝ):ℂ) := by
  simp only [truncatedSeriesPolynomial,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow]

lemma finiteExp_real_polynomial_remainder (f:WP.HigherOrder.Series) (C B:ℝ)
    (hC:0≤C) (hB:0<B) (hf0:PowerSeries.constantCoeff f=0)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ) (h:ℝ) (hh:0<h) (hwindow:4*B*((K:ℝ)+1)≤h) :
    |Real.exp (∑i∈Finset.range (K+1),PowerSeries.coeff i f/h^i)-
      ∑i∈Finset.range (K+1),PowerSeries.coeff i (WP.HigherOrder.finiteExp f)/h^i|≤
      2*Real.exp (2*C)*(2*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1) := by
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(4*B*((K:ℝ)+1)) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) hwindow
  have he := finiteExp_truncated_polynomial_remainder f C B hC hB hf0 hf K ((1/h:ℝ):ℂ) hz
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

end WP.Analysis
