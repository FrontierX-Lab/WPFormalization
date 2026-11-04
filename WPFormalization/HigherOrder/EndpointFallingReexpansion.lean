import WPFormalization.Analysis.GammaFallingBounds
import WPFormalization.HigherOrder.EndpointRationalProducts
import WPFormalization.HigherOrder.FiniteGevreyOne
import WPFormalization.HigherOrder.PainleveCoefficientBounds

/-! Uniform re-expansion of the actual finite falling-Gamma sum in the canonical endpointZ series. The original jump coefficients and formal product are identified exactly, and one shrinking Cauchy circle gives the factorial error at all orders with constants independent of the order. No analytic Painleve jump or contour premise is used in this module. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma factorial_power_shift_bound (n j : ℕ) (hjn : j≤n) :
    (j.factorial:ℝ)*(n:ℝ)^(n-j) ≤ Real.exp (n:ℝ)*(n.factorial:ℝ) := by
  have hq : (0:ℝ)<(n-j).factorial := by exact_mod_cast Nat.factorial_pos (n-j)
  have he := Real.pow_div_factorial_le_exp (n:ℝ) (Nat.cast_nonneg _) (n-j)
  calc
    _ = ((j.factorial:ℝ)*((n-j).factorial:ℝ))*((n:ℝ)^(n-j)/((n-j).factorial:ℝ)) := by field_simp
    _ ≤ (n.factorial:ℝ)*Real.exp (n:ℝ) :=
      mul_le_mul (factorial_product_cast_le n j hjn) he (by positivity) (by positivity)
    _ = _ := by ring
lemma finite_triangle_sum_exchange (f : ℕ→ℕ→ℂ) (n : ℕ) :
    (∑j∈Finset.range n,∑q∈Finset.range (n-j),f j q)=
      ∑m∈Finset.range n,∑j∈Finset.range (m+1),f j (m-j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he (j : ℕ) (hj : j∈Finset.range n) :
        (∑q∈Finset.range (n+1-j),f j q)=
          (∑q∈Finset.range (n-j),f j q)+f j (n-j) := by
      have hjn := Finset.mem_range.mp hj
      rw [show n+1-j=(n-j)+1 by omega,Finset.sum_range_succ]
    calc
      _ = (∑j∈Finset.range n,((∑q∈Finset.range (n-j),f j q)+f j (n-j)))+f n 0 := by
        rw [Finset.sum_range_succ,show n+1-n=1 by omega,Finset.sum_range_one]
        congr 1
        exact Finset.sum_congr rfl he
      _ = (∑j∈Finset.range n,∑q∈Finset.range (n-j),f j q)+
          (∑j∈Finset.range n,f j (n-j))+f n 0 := by rw [Finset.sum_add_distrib]
      _ = _ := by rw [ih,Finset.sum_range_succ,Finset.sum_range_succ,Nat.sub_self];abel
lemma endpointRationalProduct_coeff (j q : ℕ) :
    WP.coeff (endpointRationalProduct j) q=
      ((PowerSeries.coeff q (∏a∈Finset.range j,(1+C (1/2-(a:ℝ))*PowerSeries.X : Series)⁻¹):ℝ):ℂ) := by
  have he := congrArg (PowerSeries.coeff q) (endpointRationalProduct_taylor j)
  simpa only [WP.Analysis.taylor_coeff,PowerSeries.coeff_map,Complex.ofRealHom_eq_coe] using he
lemma endpointZ_coeff_sum (m : ℕ) :
    PowerSeries.coeff m endpointZ=
      ∑j∈Finset.range (m+1),(jumpCoefficient j:ℝ)*
        PowerSeries.coeff (m-j) (∏a∈Finset.range j,(1+C (1/2-(a:ℝ))*PowerSeries.X : Series)⁻¹) := by
  rw [endpointZ,PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro j hj
  rw [PowerSeries.coeff_X_pow_mul',if_pos (by have := Finset.mem_range.mp hj;omega)]
lemma endpointZ_finite_taylor_triangle (n : ℕ) (z : ℂ) :
    (∑j∈Finset.range n,(jumpCoefficient j:ℂ)*z^j*
      (∑q∈Finset.range (n-j),WP.coeff (endpointRationalProduct j) q*z^q))=
      ∑m∈Finset.range n,((PowerSeries.coeff m endpointZ:ℝ):ℂ)*z^m := by
  calc
    _ = ∑j∈Finset.range n,∑q∈Finset.range (n-j),
        (jumpCoefficient j:ℂ)*WP.coeff (endpointRationalProduct j) q*z^(j+q) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [pow_add]
      ring
    _ = ∑m∈Finset.range n,∑j∈Finset.range (m+1),
        (jumpCoefficient j:ℂ)*WP.coeff (endpointRationalProduct j) (m-j)*z^(j+(m-j)) :=
      finite_triangle_sum_exchange _ n
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [endpointZ_coeff_sum]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [endpointRationalProduct_coeff,Nat.add_sub_of_le (by have := Finset.mem_range.mp hj;omega)]
lemma endpointRationalProduct_one_error_bound (n j : ℕ) (hn : 1≤n) (hj : j<n)
    (z : ℂ) (hz : ‖z‖≤1/(4*(n:ℝ))) :
    ‖(jumpCoefficient j:ℂ)*z^j*(endpointRationalProduct j z-
      (∑q∈Finset.range (n-j),WP.coeff (endpointRationalProduct j) q*z^q))‖ ≤
      2*(64:ℝ)^n*Real.exp (n:ℝ)*(n.factorial:ℝ)*‖z‖^n := by
  have hjn : j≤n := hj.le
  have hv : ‖(jumpCoefficient j:ℂ)‖ ≤ (32:ℝ)^j*(j.factorial:ℝ) := by
    have he : (jumpCoefficient j:ℂ)=((jumpCoefficient j:ℝ):ℂ) := by norm_cast
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    exact jumpCoefficient_real_factorial_bound j
  have ht := endpointRationalProduct_taylor_remainder n j (n-j) hn hjn z hz
  have hp : (64:ℝ)^j*(2:ℝ)^(n-j)≤(64:ℝ)^n := by
    calc
      _ ≤ (64:ℝ)^j*(64:ℝ)^(n-j) := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by norm_num : (2:ℝ)≤64) _) (by positivity)
      _ = _ := by rw [←pow_add,Nat.add_sub_of_le hjn]
  have hzpow : ‖z‖^j*‖z‖^(n-j)=‖z‖^n := by rw [←pow_add,Nat.add_sub_of_le hjn]
  have h64 : (32:ℝ)^j*(2:ℝ)^j=(64:ℝ)^j := by rw [←mul_pow];norm_num
  rw [norm_mul,norm_mul,norm_pow]
  calc
    _ ≤ ((32:ℝ)^j*(j.factorial:ℝ)*‖z‖^j)*(2*(2:ℝ)^j*(2*(n:ℝ)*‖z‖)^(n-j)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hv (by positivity)) ht (norm_nonneg _) (by positivity)
    _ = 2*((32:ℝ)^j*(2:ℝ)^j)*(2:ℝ)^(n-j)*
        ((j.factorial:ℝ)*(n:ℝ)^(n-j))*(‖z‖^j*‖z‖^(n-j)) := by
      rw [mul_pow,mul_pow]
      ring
    _ = 2*((64:ℝ)^j*(2:ℝ)^(n-j))*((j.factorial:ℝ)*(n:ℝ)^(n-j))*‖z‖^n := by rw [h64,hzpow];ring
    _ ≤ 2*(64:ℝ)^n*(Real.exp (n:ℝ)*(n.factorial:ℝ))*‖z‖^n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2))
        (factorial_power_shift_bound n j hjn) (by positivity) (by positivity)
    _ = _ := by ring

lemma endpointFallingSum_reexpansion_bound (n : ℕ) (hn : 1≤n)
    (z : ℂ) (hz : ‖z‖≤1/(4*(n:ℝ))) :
    ‖(∑j∈Finset.range n,(jumpCoefficient j:ℂ)*z^j*endpointRationalProduct j z)-
        (∑m∈Finset.range n,((PowerSeries.coeff m endpointZ:ℝ):ℂ)*z^m)‖ ≤
      2*(128*Real.exp 1)^n*(n.factorial:ℝ)*‖z‖^n := by
  rw [←endpointZ_finite_taylor_triangle n z,←Finset.sum_sub_distrib]
  have heq : (fun j:ℕ => (jumpCoefficient j:ℂ)*z^j*endpointRationalProduct j z-
        (jumpCoefficient j:ℂ)*z^j*(∑q∈Finset.range (n-j),WP.coeff (endpointRationalProduct j) q*z^q))=
      fun j:ℕ => (jumpCoefficient j:ℂ)*z^j*(endpointRationalProduct j z-
        (∑q∈Finset.range (n-j),WP.coeff (endpointRationalProduct j) q*z^q)) := by funext j;ring
  rw [heq]
  calc
    _ ≤ ∑j∈Finset.range n,‖(jumpCoefficient j:ℂ)*z^j*(endpointRationalProduct j z-
        (∑q∈Finset.range (n-j),WP.coeff (endpointRationalProduct j) q*z^q))‖ := norm_sum_le _ _
    _ ≤ ∑j∈Finset.range n,2*(64:ℝ)^n*Real.exp (n:ℝ)*(n.factorial:ℝ)*‖z‖^n := by
      apply Finset.sum_le_sum
      intro j hj
      exact endpointRationalProduct_one_error_bound n j hn (Finset.mem_range.mp hj) z hz
    _ = (n:ℝ)*(2*(64:ℝ)^n*Real.exp (n:ℝ)*(n.factorial:ℝ)*‖z‖^n) := by simp
    _ ≤ (2:ℝ)^n*(2*(64:ℝ)^n*Real.exp (n:ℝ)*(n.factorial:ℝ)*‖z‖^n) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show n ≤ (2:ℕ)^n from Nat.le_of_lt Nat.lt_two_pow_self)
    _ = _ := by
      have he : Real.exp (n:ℝ)=(Real.exp 1)^n := by simpa using Real.exp_nat_mul 1 n
      rw [he,mul_pow]
      have hp : (2:ℝ)^n*(64:ℝ)^n=(128:ℝ)^n := by rw [←mul_pow];norm_num
      calc
        _ = 2*((2:ℝ)^n*(64:ℝ)^n)*(Real.exp 1)^n*(n.factorial:ℝ)*‖z‖^n := by ring
        _ = _ := by rw [hp];ring

lemma endpointRationalProduct_real (j : ℕ) (t : ℝ) :
    endpointRationalProduct j (t:ℂ)=((∏a∈Finset.range j,(1+(1/2-(a:ℝ))*t)⁻¹:ℝ):ℂ) := by
  unfold endpointRationalProduct
  push_cast
  rfl
lemma gamma_endpoint_falling_product (h : ℝ) (j : ℕ) (hh : 0<h) (hj : (j:ℝ)≤h) :
    Real.Gamma (h+3/2-(j:ℝ))/Real.Gamma (h+3/2)=
      h⁻¹^j*(∏a∈Finset.range j,(1+(1/2-(a:ℝ))*h⁻¹)⁻¹) := by
  have hx : 0<h+3/2-(j:ℝ) := by linarith
  rw [WP.Analysis.gamma_falling_ratio_product (h+3/2) j hx]
  rw [←Finset.prod_range_reflect]
  calc
    _ = ∏a∈Finset.range j,h⁻¹*(1+(1/2-(a:ℝ))*h⁻¹)⁻¹ := by
      apply Finset.prod_congr rfl
      intro a ha
      have haj : a<j := Finset.mem_range.mp ha
      have he : h+3/2-(j:ℝ)+((j-1-a:ℕ):ℝ)=h+1/2-(a:ℝ) := by
        have han : a≤j-1 := by omega
        rw [Nat.cast_sub han,Nat.cast_sub (by omega : 1≤j)]
        push_cast
        ring
      rw [he]
      have ht : h+1/2-(a:ℝ)=h*(1+(1/2-(a:ℝ))*h⁻¹) := by field_simp;ring
      rw [ht,mul_inv_rev]
      ring
    _ = _ := by rw [Finset.prod_mul_distrib];simp

lemma gamma_endpoint_falling_sum_reexpansion (h : ℝ) (n : ℕ) (hn : 1≤n)
    (hlarge : 4*(n:ℝ)≤h) :
    |(∑j∈Finset.range n,(jumpCoefficient j:ℝ)*
        (Real.Gamma (h+3/2-(j:ℝ))/Real.Gamma (h+3/2)))-
      (∑m∈Finset.range n,PowerSeries.coeff m endpointZ*h⁻¹^m)| ≤
      2*(128*Real.exp 1)^n*(n.factorial:ℝ)*h⁻¹^n := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hh : 0<h := by linarith
  have hz : ‖((h⁻¹:ℝ):ℂ)‖≤1/(4*(n:ℝ)) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤h⁻¹)]
    simpa only [one_div] using inv_anti₀ (by positivity : (0:ℝ)<4*(n:ℝ)) hlarge
  have hb := endpointFallingSum_reexpansion_bound n hn ((h⁻¹:ℝ):ℂ) hz
  have hf : (∑j∈Finset.range n,(jumpCoefficient j:ℂ)*((h⁻¹:ℝ):ℂ)^j*
      endpointRationalProduct j ((h⁻¹:ℝ):ℂ))=
      Complex.ofRealHom (∑j∈Finset.range n,(jumpCoefficient j:ℝ)*
        (Real.Gamma (h+3/2-(j:ℝ))/Real.Gamma (h+3/2))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : (j:ℝ)≤n := by exact_mod_cast (Finset.mem_range.mp hj).le
    have hjh : (j:ℝ)≤h := by linarith
    rw [endpointRationalProduct_real,gamma_endpoint_falling_product h j hh hjh]
    simp only [Complex.ofRealHom_eq_coe]
    push_cast <;> ring
  have hp : (∑m∈Finset.range n,((PowerSeries.coeff m endpointZ:ℝ):ℂ)*((h⁻¹:ℝ):ℂ)^m)=
      Complex.ofRealHom (∑m∈Finset.range n,PowerSeries.coeff m endpointZ*h⁻¹^m) := by
    simp only [Complex.ofRealHom_eq_coe]
    push_cast <;> rfl
  rw [hf,hp,←map_sub] at hb
  simpa only [Complex.ofRealHom_eq_coe,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0≤h⁻¹)] using hb

end WP.HigherOrder
