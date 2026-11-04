import WPFormalization.Statements.Basic
/-! Positive factorial-square Bessel translation sums have uniformly summable quadratic degree moments. This elementary majorant is proved using the ordinary exponential series, with no new external input. -/
noncomputable section
namespace WP.Analysis

lemma boundary_exp_hasSum (x : ℝ) : HasSum (fun n : ℕ => x^n/(n.factorial:ℝ)) (Real.exp x) := by
  simpa only [←Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

lemma boundary_kernel_factorial_bound (b : ℕ) (z K : ℝ) (hz : 0 ≤ z)
    (hK : HasSum (fun a : ℕ => z^a/((a.factorial:ℝ)*((a+b).factorial:ℝ))) K) :
    0 ≤ K ∧ K ≤ Real.exp z/(b.factorial:ℝ) := by
  have hnon (a : ℕ) : 0 ≤ z^a/((a.factorial:ℝ)*((a+b).factorial:ℝ)) := by positivity
  have hupper := (boundary_exp_hasSum z).div_const (b.factorial:ℝ)
  have hb (a : ℕ) : z^a/((a.factorial:ℝ)*((a+b).factorial:ℝ)) ≤
      (z^a/(a.factorial:ℝ))/(b.factorial:ℝ) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left (pow_nonneg hz a) (by positivity)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.factorial_le (Nat.le_add_left b a)) (by positivity))
  refine ⟨hK.nonneg hnon,?_⟩
  rw [←hK.tsum_eq,←hupper.tsum_eq]
  exact hK.summable.tsum_le_tsum hb hupper.summable

lemma boundary_polynomial_square_bound (b : ℕ) : ((b:ℝ)+1)^2 ≤ (4:ℝ)^b := by
  have hn : b+1 ≤ 2^b := Nat.lt_two_pow_self
  have hr : (b:ℝ)+1 ≤ (2:ℝ)^b := by exact_mod_cast hn
  calc
    _ ≤ ((2:ℝ)^b)^2 := pow_le_pow_left₀ (by positivity) hr 2
    _ = (4:ℝ)^b := by rw [←pow_mul, Nat.mul_comm b 2, pow_mul];norm_num

lemma boundary_oddFactorial_one_le (b : ℕ) : (1:ℝ) ≤ (WP.oddFactorial b:ℝ) := by
  have hn : 1 ≤ WP.oddFactorial b := Finset.one_le_prod (fun i _ => by omega)
  exact_mod_cast hn

lemma boundary_weighted_kernel_moment (r t Y : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) (hY : 0 ≤ Y)
    (K : ℕ → ℝ) (hK : ∀ b, HasSum (fun a : ℕ => (t*Y)^a/
      ((a.factorial:ℝ)*((a+b).factorial:ℝ))) (K b)) :
    Summable (fun b : ℕ => ((b:ℝ)+1)^2 *
      (r^b/(WP.oddFactorial b:ℝ)*t^b*K b)) ∧
    (∑' b : ℕ, ((b:ℝ)+1)^2 *
      (r^b/(WP.oddFactorial b:ℝ)*t^b*K b)) ≤ Real.exp (t*Y)*Real.exp (4*r*t) := by
  have hk := fun b => boundary_kernel_factorial_bound b (t*Y) (K b) (mul_nonneg ht hY) (hK b)
  have hs := (boundary_exp_hasSum (4*r*t)).mul_left (Real.exp (t*Y))
  have hpos (b : ℕ) : 0 ≤ ((b:ℝ)+1)^2*(r^b/(WP.oddFactorial b:ℝ)*t^b*K b) := by
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg
      (div_nonneg (pow_nonneg hr _) (zero_le_one.trans (boundary_oddFactorial_one_le b)))
      (pow_nonneg ht _)) (hk b).1)
  have hterm (b : ℕ) : ((b:ℝ)+1)^2*(r^b/(WP.oddFactorial b:ℝ)*t^b*K b) ≤
      Real.exp (t*Y)*((4*r*t)^b/(b.factorial:ℝ)) := by
    have hodd : r^b/(WP.oddFactorial b:ℝ) ≤ r^b :=
      div_le_self (pow_nonneg hr _) (boundary_oddFactorial_one_le b)
    calc
      _ ≤ ((b:ℝ)+1)^2*(r^b*t^b*(Real.exp (t*Y)/(b.factorial:ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul_of_nonneg_right hodd (pow_nonneg ht b))
            (hk b).2 (hk b).1 (by positivity)) (sq_nonneg _)
      _ ≤ (4:ℝ)^b*(r^b*t^b*(Real.exp (t*Y)/(b.factorial:ℝ))) := by
        exact mul_le_mul_of_nonneg_right (boundary_polynomial_square_bound b) (by positivity)
      _ = _ := by rw [mul_pow,mul_pow];ring
  have hsum := Summable.of_nonneg_of_le hpos hterm hs.summable
  exact ⟨hsum,by rw [←hs.tsum_eq];exact hsum.tsum_le_tsum hterm hs.summable⟩
end WP.Analysis
