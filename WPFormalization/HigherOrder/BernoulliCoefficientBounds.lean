import WPFormalization.HigherOrder.EndpointFormal
/-! Finite Bernoulli and Gamma-log coefficient bounds for the canonical endpoint construction. The estimates follow from Mathlib identities, with no added asymptotic input. -/
noncomputable section
namespace WP.HigherOrder
lemma bernoulli_triangular_recursion (n : ℕ) (hn : 1 ≤ n) :
    bernoulli n=-(∑ k∈Finset.range n,(Nat.choose (n+1) k:ℚ)*bernoulli k)/((n:ℚ)+1) := by
  have he := sum_bernoulli (n+1)
  rw [if_neg (by omega : n+1 ≠ 1),Finset.sum_range_succ,Nat.choose_succ_self_right,
    Nat.cast_add,Nat.cast_one] at he
  apply (eq_div_iff (by positivity : (n:ℚ)+1 ≠ 0)).2
  linarith
lemma choose_mul_factorial_le (n k : ℕ) (hk : k ≤ n) :
    (Nat.choose n k:ℚ)*(k.factorial:ℚ) ≤ n.factorial := by
  have h0 : 1 ≤ (n-k).factorial := Nat.succ_le_of_lt (Nat.factorial_pos _)
  have h := Nat.mul_le_mul_left (Nat.choose n k*k.factorial) h0
  rw [mul_one,Nat.choose_mul_factorial_mul_factorial hk] at h
  exact_mod_cast h
lemma bernoulli_factorial_bound (n : ℕ) :
    |bernoulli n| ≤ (2:ℚ)^n*(n.factorial:ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n=0
      · subst n;norm_num
      have hn : 1 ≤ n := by omega
      have hnQ : (0:ℚ)<n+1 := by positivity
      rw [bernoulli_triangular_recursion n hn,abs_div,abs_neg,abs_of_pos hnQ]
      apply (div_le_iff₀ hnQ).2
      have hterm (k : ℕ) (hk : k∈Finset.range n) :
          |(Nat.choose (n+1) k:ℚ)*bernoulli k| ≤ (2:ℚ)^k*((n+1).factorial:ℚ) := by
        have hk' := Finset.mem_range.mp hk
        rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
        calc
          _ ≤ (Nat.choose (n+1) k:ℚ)*((2:ℚ)^k*(k.factorial:ℚ)) :=
            mul_le_mul_of_nonneg_left (ih k hk') (Nat.cast_nonneg _)
          _ = (2:ℚ)^k*((Nat.choose (n+1) k:ℚ)*(k.factorial:ℚ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (choose_mul_factorial_le (n+1) k (by omega)) (by positivity)
      have hgeom : (∑ k∈Finset.range n,(2:ℚ)^k) ≤ 2^n := by
        have he := geom_sum_mul (2:ℚ) n
        norm_num at he
        linarith
      calc
        _ ≤ ∑ k∈Finset.range n,|(Nat.choose (n+1) k:ℚ)*bernoulli k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k∈Finset.range n,(2:ℚ)^k*((n+1).factorial:ℚ) := Finset.sum_le_sum hterm
        _ = ((n+1).factorial:ℚ)*(∑ k∈Finset.range n,(2:ℚ)^k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ ≤ ((n+1).factorial:ℚ)*(2:ℚ)^n := mul_le_mul_of_nonneg_left hgeom (by positivity)
        _ = _ := by rw [Nat.factorial_succ];push_cast;ring
lemma bernoulliPolynomialValue_factorial_bound (m : ℕ) (a : ℚ) :
    |bernoulliPolynomialValue m a| ≤ (2*(2+|a|))^m*(m.factorial:ℚ) := by
  let B : ℚ := 2+|a|
  have hB : 0 ≤ B := by dsimp [B];positivity
  have h2B : 2 ≤ B := by dsimp [B];linarith [abs_nonneg a]
  have haB : |a| ≤ B := by dsimp [B];linarith
  have ht (k : ℕ) (hk : k∈Finset.range (m+1)) :
      |(Nat.choose m k:ℚ)*bernoulli k*a^(m-k)| ≤ B^m*(m.factorial:ℚ) := by
    have hkm : k ≤ m := by have := Finset.mem_range.mp hk;omega
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_pow]
    calc
      _ ≤ ((Nat.choose m k:ℚ)*((2:ℚ)^k*(k.factorial:ℚ)))*|a|^(m-k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bernoulli_factorial_bound k) (Nat.cast_nonneg _)) (by positivity)
      _ = (Nat.choose m k:ℚ)*(k.factorial:ℚ)*((2:ℚ)^k*|a|^(m-k)) := by ring
      _ ≤ (m.factorial:ℚ)*(B^k*B^(m-k)) := mul_le_mul
        (choose_mul_factorial_le m k hkm)
        (mul_le_mul (pow_le_pow_left₀ (by norm_num) h2B k) (pow_le_pow_left₀ (abs_nonneg _) haB (m-k)) (by positivity) (by positivity))
        (by positivity) (by positivity)
      _ = _ := by rw [←pow_add,Nat.add_sub_of_le hkm];ring
  unfold bernoulliPolynomialValue
  calc
    _ ≤ ∑ k∈Finset.range (m+1),|(Nat.choose m k:ℚ)*bernoulli k*a^(m-k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k∈Finset.range (m+1),B^m*(m.factorial:ℚ) := Finset.sum_le_sum ht
    _ = ((m:ℚ)+1)*(B^m*(m.factorial:ℚ)) := by simp
    _ ≤ (2:ℚ)^m*(B^m*(m.factorial:ℚ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.succ_le_of_lt (show m < (2:ℕ)^m from Nat.lt_two_pow_self)
    _ = _ := by dsimp [B];rw [mul_pow];ring
end WP.HigherOrder
namespace WP.HigherOrder
open PowerSeries
lemma gammaRatioLog_factorial_bound (n : ℕ) :
    |PowerSeries.coeff n (gammaRatioLog (3/2))| ≤ 14*(7:ℝ)^n*(n.factorial:ℝ) := by
  by_cases hn0 : n=0
  · subst n
    norm_num [PowerSeries.coeff_zero_eq_constantCoeff]
  have hn1 : 1 ≤ n := by omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0:ℝ)<n := by linarith
  have hb3 : |(bernoulliPolynomialValue (n+1) (3/2):ℝ)| ≤
      (7:ℝ)^(n+1)*((n+1).factorial:ℝ) := by
    have he := bernoulliPolynomialValue_factorial_bound (n+1) (3/2)
    norm_num at he
    exact_mod_cast he
  have hb0 : |(bernoulliPolynomialValue (n+1) 0:ℝ)| ≤
      (7:ℝ)^(n+1)*((n+1).factorial:ℝ) := by
    have he := bernoulliPolynomialValue_factorial_bound (n+1) 0
    norm_num at he
    have heR : |(bernoulliPolynomialValue (n+1) 0:ℝ)| ≤
        (4:ℝ)^(n+1)*((n+1).factorial:ℝ) := by exact_mod_cast he
    exact heR.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num) (by norm_num) (n+1)) (by positivity))
  have hnum : |(bernoulliPolynomialValue (n+1) (3/2):ℝ)-
      (bernoulliPolynomialValue (n+1) 0:ℝ)| ≤ 2*(7:ℝ)^(n+1)*((n+1).factorial:ℝ) := by
    exact ((abs_sub _ _).trans (add_le_add hb3 hb0)).trans_eq (by ring)
  rw [gammaRatioLog,PowerSeries.coeff_mk,if_neg hn0,abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
  push_cast
  rw [abs_of_pos (by positivity : (0:ℝ)<(n:ℝ)*(n+1))]
  calc
    _ ≤ (2*(7:ℝ)^(n+1)*((n+1).factorial:ℝ))/((n:ℝ)*(n+1)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (14*(7:ℝ)^n*(n.factorial:ℝ))/(n:ℝ) := by
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
      field_simp
      ring
    _ ≤ _ := div_le_self (by positivity) hnR
end WP.HigherOrder
