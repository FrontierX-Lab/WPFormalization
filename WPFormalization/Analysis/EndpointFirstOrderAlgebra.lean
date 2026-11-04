import WPFormalization.Analysis.FirstOrderRatioAlgebra
/-! Scalar first-order products, square roots and finite scale shifts with quadratic errors. -/
noncomputable section
namespace WP.Analysis
lemma unit_first_order_product (a b x y C D h : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hh : 1 ≤ h)
    (hx : |x-(1+a/h)| ≤ C/h^2) (hy : |y-(1+b/h)| ≤ D/h^2) :
    |x*y-(1+(a+b)/h)| ≤
      ((1+|a|+|b|)^2+4*(1+|a|+|b|)*(C+D)+(C+D)^2)/h^2 := by
  have hh0 : 0 < h := by linarith
  have ht : h⁻¹ ∈ Set.Icc (0:ℝ) 1 := ⟨by positivity,inv_le_one_of_one_le₀ hh⟩
  have hM : 0 ≤ 1+|a|+|b| := by positivity
  have he := first_order_mul_error 1 a 1 b x y (1+|a|+|b|) (C+D) h⁻¹ hM
    (by positivity) ht (by simp only [abs_one];linarith [abs_nonneg a,abs_nonneg b])
    (by linarith [abs_nonneg b]) (by simp only [abs_one];linarith [abs_nonneg a,abs_nonneg b])
    (by linarith [abs_nonneg a])
    (by simpa only [div_eq_mul_inv,inv_pow] using
      hx.trans (div_le_div_of_nonneg_right (by linarith : C ≤ C+D) (sq_nonneg h)))
    (by simpa only [div_eq_mul_inv,inv_pow] using
      hy.trans (div_le_div_of_nonneg_right (by linarith : D ≤ C+D) (sq_nonneg h)))
  simpa only [one_mul,mul_one,←add_div,div_eq_mul_inv,inv_pow,add_comm b a] using he
lemma inverse_one_add_second_error (u : ℝ) (hu : 0 ≤ u) :
    |(1+u)⁻¹-(1-u)| ≤ u^2 := by
  have hp : 0 < 1+u := by positivity
  have he : (1+u)⁻¹-(1-u)=u^2/(1+u) := by field_simp;ring
  rw [he,abs_of_nonneg (by positivity : 0 ≤ u^2/(1+u))]
  exact (div_le_iff₀ hp).2 (by nlinarith [mul_nonneg (sq_nonneg u) hu])
lemma sqrt_one_add_second_error (u : ℝ) (hu : 0 ≤ u) :
    |Real.sqrt (1+u)-(1+u/2)| ≤ u^2/8 := by
  have hs0 := Real.sqrt_nonneg (1+u)
  have hs1 : 1 ≤ Real.sqrt (1+u) := Real.one_le_sqrt.2 (by linarith)
  have hs2 := Real.sq_sqrt (by positivity : 0 ≤ 1+u)
  have hsU : Real.sqrt (1+u) ≤ 1+u/2 := by nlinarith
  have hsq : (Real.sqrt (1+u)-1)^2 ≤ u^2/4 := by
    have hx : 0 ≤ Real.sqrt (1+u)-1 := by linarith
    have hy : Real.sqrt (1+u)-1 ≤ u/2 := by linarith
    nlinarith
  rw [abs_of_nonpos (by linarith : Real.sqrt (1+u)-(1+u/2) ≤ 0)]
  nlinarith
lemma reverse_unit_shift_error (x a C h : ℝ) (hC : 0 ≤ C) (hh : 1 ≤ h)
    (hx : |x-(1+a/h)| ≤ C/h^2) :
    |x-(1+a/(h+1))| ≤ 4*(C+|a|)/(h+1)^2 := by
  have hh0 : 0 < h := by linarith
  have hhp : 0 < h+1 := by positivity
  have hc : |(1+a/h)-(1+a/(h+1))| ≤ |a|/h^2 := by
    have he : (1+a/h)-(1+a/(h+1))=a/(h*(h+1)) := by field_simp;ring
    rw [he,abs_div,abs_of_pos (mul_pos hh0 hhp)]
    apply div_le_div_of_nonneg_left (abs_nonneg a) (sq_pos_of_pos hh0)
    nlinarith
  have hb : |x-(1+a/(h+1))| ≤ (C+|a|)/h^2 := by
    calc
      _ ≤ |x-(1+a/h)|+|(1+a/h)-(1+a/(h+1))| := abs_sub_le _ _ _
      _ ≤ C/h^2+|a|/h^2 := add_le_add hx hc
      _ = _ := by ring
  apply hb.trans
  apply (div_le_div_iff₀ (sq_pos_of_pos hh0) (sq_pos_of_pos hhp)).2
  have hden : (h+1)^2 ≤ 4*h^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ C+|a| by positivity)]
end WP.Analysis

noncomputable section
namespace WP.Analysis
lemma log_second_error_near_one (x : ℝ) (hx : 1/2 ≤ x) :
    |Real.log x-(x-1)| ≤ 2*(x-1)^2 := by
  have hx0 : 0 < x := by linarith
  have hu := Real.log_le_sub_one_of_pos hx0
  have hl := Real.one_sub_inv_le_log_of_pos hx0
  have heq : (x-1)-(1-x⁻¹)=(x-1)^2/x := by field_simp <;> ring
  rw [abs_of_nonpos (by linarith : Real.log x-(x-1) ≤ 0)]
  calc
    _ ≤ (x-1)-(1-x⁻¹) := by linarith
    _ = (x-1)^2/x := heq
    _ ≤ 2*(x-1)^2 := (div_le_iff₀ hx0).2 (by nlinarith [mul_nonneg (sq_nonneg (x-1)) (show 0 ≤ 2*x-1 by linarith)])
lemma log_unit_first_order_error (x a C h : ℝ) (hC : 0 ≤ C) (hh : 1 ≤ h)
    (hlarge : 2*(|a|+C) ≤ h) (hx : |x-(1+a/h)| ≤ C/h^2) :
    |Real.log x-a/h| ≤ (2*(|a|+C)^2+C)/h^2 := by
  have hh0 : 0 < h := by linarith
  have hpow : h ≤ h^2 := by nlinarith
  have hdiff : |x-1| ≤ (|a|+C)/h := by
    calc
      _ ≤ |x-(1+a/h)|+|(1+a/h)-1| := abs_sub_le _ _ _
      _ ≤ C/h^2+|a|/h := by rw [add_sub_cancel_left,abs_div,abs_of_pos hh0];exact add_le_add hx le_rfl
      _ ≤ C/h+|a|/h := add_le_add (div_le_div_of_nonneg_left hC hh0 hpow) le_rfl
      _ = _ := by ring
  have hhalf : |x-1| ≤ 1/2 := hdiff.trans ((div_le_iff₀ hh0).2 (by linarith))
  have hxp : 1/2 ≤ x := by have hb := (abs_le.mp hhalf).1;linarith
  have hs : (x-1)^2 ≤ (|a|+C)^2/h^2 := by
    have hb := pow_le_pow_left₀ (abs_nonneg (x-1)) hdiff 2
    simpa only [sq_abs,div_pow] using hb
  calc
    _ ≤ |Real.log x-(x-1)|+|(x-1)-a/h| := abs_sub_le _ _ _
    _ ≤ 2*(x-1)^2+C/h^2 := add_le_add (log_second_error_near_one x hxp) (by convert hx using 1 <;> congr 1 <;> ring)
    _ ≤ 2*((|a|+C)^2/h^2)+C/h^2 := add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num)) le_rfl
    _ = _ := by ring
end WP.Analysis
