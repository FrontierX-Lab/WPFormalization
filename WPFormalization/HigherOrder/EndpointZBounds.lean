import WPFormalization.HigherOrder.PainleveCoefficientBounds
import WPFormalization.HigherOrder.ShiftCoefficientBounds
/-! The genuine endpointZ series has a Gevrey-one coefficient bound, using the actual jump recurrence and the exact finite shifted inverse factors. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma endpointZ_product_coeff_bound (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    |PowerSeries.coeff (n-j) (∏ a∈Finset.range j,
      (1+C (1/2-(a:ℝ))*PowerSeries.X : Series)⁻¹)| ≤
      (n:ℝ)^(2*(n-j))/((n-j).factorial:ℝ) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (hj.trans hjn)
  have hp : (∏ a∈Finset.range j,(1+C (1/2-(a:ℝ))*PowerSeries.X : Series)⁻¹)=
      ∏ a∈Finset.range j,((1-C ((a:ℝ)-1/2)*PowerSeries.X : Series)⁻¹)^1 := by
    apply Finset.prod_congr rfl
    intro a ha
    rw [pow_one]
    congr 1
    rw [show (1/2:ℝ)-a= -((a:ℝ)-1/2) by ring]
    simp only [map_neg,neg_mul,sub_eq_add_neg]
  rw [hp]
  apply inverse_linear_product_coeff_normalized (Finset.range j) (fun _ => 1)
    (fun a => (a:ℝ)-1/2) (n:ℝ) (n-j) n
  · simpa using hj
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
    omega
  · intro a ha
    have haR : (a:ℝ) ≤ n := by exact_mod_cast (show a ≤ n from (Finset.mem_range.mp ha).le.trans hjn)
    apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) a]
  · exact le_rfl
lemma factorial_shift_power_bound (n j : ℕ) (hjn : j ≤ n) :
    (j.factorial:ℝ)*(n:ℝ)^(2*(n-j))/((n-j).factorial:ℝ) ≤
      Real.exp (2*(n:ℝ))*(n.factorial:ℝ) := by
  let q := n-j
  have hfact : (j.factorial:ℝ)*(q.factorial:ℝ) ≤ n.factorial := by
    have he := Nat.le_of_dvd (Nat.factorial_pos (j+q)) (Nat.factorial_mul_factorial_dvd_factorial_add j q)
    have hq : j+q=n := by dsimp [q];omega
    rw [hq] at he
    exact_mod_cast he
  have hq0 : (0:ℝ)<q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hexp := Real.pow_div_factorial_le_exp (n:ℝ) (Nat.cast_nonneg n) q
  have hpower : ((n:ℝ)^q/(q.factorial:ℝ))^2 ≤ Real.exp (2*(n:ℝ)) := by
    have he := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (n:ℝ)^q/(q.factorial:ℝ)) hexp 2
    convert he using 1
    rw [←Real.exp_nat_mul]
    norm_num
  calc
    _ = ((j.factorial:ℝ)*(q.factorial:ℝ))*((n:ℝ)^q/(q.factorial:ℝ))^2 := by
      change (j.factorial:ℝ)*(n:ℝ)^(2*q)/(q.factorial:ℝ)=_
      rw [Nat.mul_comm 2 q,pow_mul]
      field_simp
    _ ≤ (n.factorial:ℝ)*Real.exp (2*(n:ℝ)) := mul_le_mul hfact hpower (by positivity) (by positivity)
    _ = _ := by ring
lemma endpointZ_factorial_bound (n : ℕ) :
    |PowerSeries.coeff n endpointZ| ≤ (64*Real.exp 2)^n*(n.factorial:ℝ) := by
  by_cases hn0 : n=0
  · subst n
    norm_num [PowerSeries.coeff_zero_eq_constantCoeff]
  have hn1 : 1 ≤ n := by omega
  have ht (j : ℕ) (hj : j∈Finset.range (n+1)) :
      |(jumpCoefficient j:ℝ)*PowerSeries.coeff n
        ((PowerSeries.X:Series)^j*∏ a∈Finset.range j,(1+C (1/2-(a:ℝ))*PowerSeries.X)⁻¹)| ≤
      (32:ℝ)^n*Real.exp (2*(n:ℝ))*(n.factorial:ℝ) := by
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj;omega
    by_cases hj0 : j=0
    · subst j
      have hb : (0:ℝ) ≤ (32:ℝ)^n*Real.exp (2*(n:ℝ))*(n.factorial:ℝ) := by positivity
      simpa [hn0] using hb
    have hj1 : 1 ≤ j := by omega
    rw [PowerSeries.coeff_X_pow_mul',if_pos hjn,abs_mul]
    calc
      _ ≤ ((32:ℝ)^j*(j.factorial:ℝ))*((n:ℝ)^(2*(n-j))/((n-j).factorial:ℝ)) :=
        mul_le_mul (jumpCoefficient_real_factorial_bound j) (endpointZ_product_coeff_bound n j hj1 hjn)
          (abs_nonneg _) (by positivity)
      _ = (32:ℝ)^j*((j.factorial:ℝ)*(n:ℝ)^(2*(n-j))/((n-j).factorial:ℝ)) := by ring
      _ ≤ (32:ℝ)^j*(Real.exp (2*(n:ℝ))*(n.factorial:ℝ)) :=
        mul_le_mul_of_nonneg_left (factorial_shift_power_bound n j hjn) (by positivity)
      _ ≤ (32:ℝ)^n*Real.exp (2*(n:ℝ))*(n.factorial:ℝ) := by
        have he := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤32) hjn)
          (show 0 ≤ Real.exp (2*(n:ℝ))*(n.factorial:ℝ) by positivity)
        convert he using 1 <;> ring
  rw [endpointZ,PowerSeries.coeff_mk]
  calc
    _ ≤ ∑ j∈Finset.range (n+1),|(jumpCoefficient j:ℝ)*PowerSeries.coeff n
      ((PowerSeries.X:Series)^j*∏ a∈Finset.range j,(1+C (1/2-(a:ℝ))*PowerSeries.X)⁻¹)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j∈Finset.range (n+1),(32:ℝ)^n*Real.exp (2*(n:ℝ))*(n.factorial:ℝ) := Finset.sum_le_sum ht
    _ = ((n:ℝ)+1)*((32:ℝ)^n*Real.exp (2*(n:ℝ))*(n.factorial:ℝ)) := by simp
    _ ≤ (2:ℝ)^n*((32:ℝ)^n*Real.exp (2*(n:ℝ))*(n.factorial:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.succ_le_of_lt (show n < (2:ℕ)^n from Nat.lt_two_pow_self)
    _ = _ := by
      have he : Real.exp (2*(n:ℝ))=(Real.exp 2)^n := by rw [mul_comm,Real.exp_nat_mul]
      rw [he]
      have hp : (2:ℝ)^n*32^n=(64:ℝ)^n := by rw [←mul_pow];norm_num
      calc
        _ = ((2:ℝ)^n*32^n)*((Real.exp 2)^n*(n.factorial:ℝ)) := by ring
        _ = (64:ℝ)^n*((Real.exp 2)^n*(n.factorial:ℝ)) := by rw [hp]
        _ = _ := by rw [mul_pow];ring
end WP.HigherOrder
