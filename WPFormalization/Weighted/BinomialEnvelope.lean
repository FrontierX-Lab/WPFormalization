import Mathlib
/-! A finite binomial mass bound at the mode/mean, sufficient for the weighted
label envelope after exponential damping. It uses only the binomial recurrence,
the exact first moment, and a finite Markov estimate; no Stirling or local-limit
assumption is used. The resulting polynomial factor in k remains summable. -/
noncomputable section
namespace WP
def binomialWeight (N : ℕ) (x : ℝ) (j : ℕ) : ℝ := (N.choose j : ℝ)*x^j
lemma binomialWeight_nonneg (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
    0 ≤ binomialWeight N x j := by unfold binomialWeight; positivity
lemma binomialWeight_step (N j : ℕ) (x : ℝ) :
    (j+1 : ℕ)*binomialWeight N x (j+1) =
      (N-j : ℕ)*x*binomialWeight N x j := by
  have he := Nat.choose_succ_right_eq N j
  have heR : (N.choose (j+1) : ℝ)*(j+1) = (N.choose j : ℝ)*(N-j : ℕ) := by exact_mod_cast he
  unfold binomialWeight
  rw [pow_succ]
  push_cast
  nlinarith [show (N.choose (j+1) : ℝ)*((j : ℝ)+1)*x^j*x =
      (N.choose j : ℝ)*(N-j : ℕ)*x^j*x by rw [heR]]
lemma maximum_of_nat_steps (f : ℕ → ℝ) (k : ℕ)
    (hup : ∀ j, j < k → f j ≤ f (j+1))
    (hdown : ∀ j, k ≤ j → f (j+1) ≤ f j) (j : ℕ) : f j ≤ f k := by
  rcases le_total j k with hj | hj
  · have he : ∀ n : ℕ, j ≤ n → n ≤ k → f j ≤ f n := by
      intro n hjn
      induction n, hjn using Nat.le_induction with
      | base => intro h; exact le_rfl
      | succ n hn ih => intro h; exact (ih (by omega)).trans (hup n (by omega))
    exact he k hj le_rfl
  · induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact (hdown j hj).trans ih
lemma binomialWeight_mode (N k : ℕ) (hk : 1 ≤ k) (hN : 2*k ≤ N) (j : ℕ) :
    binomialWeight N ((k : ℝ)/(N-k : ℕ)) j ≤
      binomialWeight N ((k : ℝ)/(N-k : ℕ)) k := by
  have hNk : 0 < N-k := by omega
  have hNkR : (0 : ℝ) < (N-k : ℕ) := by exact_mod_cast hNk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hx : 0 ≤ (k : ℝ)/(N-k : ℕ) := div_nonneg hkR.le hNkR.le
  apply maximum_of_nat_steps
  · intro i hi
    have hiN : i ≤ N := by omega
    have he := binomialWeight_step N i ((k : ℝ)/(N-k : ℕ))
    have hcoef : (i+1 : ℕ) ≤ (N-i : ℕ)*((k : ℝ)/(N-k : ℕ)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hNkR).mpr
      rw [Nat.cast_sub hiN,Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]
      have hiR : (i : ℝ)+1 ≤ k := by exact_mod_cast (show i+1 ≤ k by omega)
      have hiMul := mul_le_mul_of_nonneg_left hiR (show (0 : ℝ) ≤ N by positivity)
      nlinarith [hiMul]
    have hW := binomialWeight_nonneg N _ hx i
    have hmul := mul_le_mul_of_nonneg_right hcoef hW
    have hip : (0 : ℝ) < (i+1 : ℕ) := by positivity
    exact (mul_le_mul_iff_right₀ hip).mp (hmul.trans_eq he.symm)
  · intro i hi
    by_cases hiN : i ≤ N
    · have he := binomialWeight_step N i ((k : ℝ)/(N-k : ℕ))
      have hcoef : (N-i : ℕ)*((k : ℝ)/(N-k : ℕ)) ≤ (i+1 : ℕ) := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hNkR).mpr
        rw [Nat.cast_sub hiN,Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]
        have hiR : (k : ℝ) ≤ i := by exact_mod_cast hi
        have hNR : (2 : ℝ)*k ≤ N := by exact_mod_cast hN
        have hiMul := mul_le_mul_of_nonneg_left hiR (show (0 : ℝ) ≤ N by positivity)
        nlinarith [hiMul]
      have hW := binomialWeight_nonneg N _ hx i
      have hmul := mul_le_mul_of_nonneg_right hcoef hW
      have hip : (0 : ℝ) < (i+1 : ℕ) := by positivity
      exact (mul_le_mul_iff_right₀ hip).mp (he.le.trans hmul)
    · have hni : N < i := by omega
      simp only [binomialWeight,Nat.choose_eq_zero_of_lt hni,
        Nat.choose_eq_zero_of_lt (show N < i+1 by omega),Nat.cast_zero,zero_mul,le_refl]
lemma binomialWeight_sum (N : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range (N+1), binomialWeight N x j) = (1+x)^N := by
  rw [show 1+x=x+1 by ring,add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [binomialWeight,one_pow,mul_one]
  ring
lemma binomialWeight_first_moment (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    (∑ j ∈ Finset.range (N+1), (j : ℝ)*binomialWeight N x j) =
      (N : ℝ)*x*(1+x)^(N-1) := by
  have hN' : N-1+1=N := by omega
  have hterm (j : ℕ) : (j+1 : ℕ)*binomialWeight N x (j+1) =
      (N : ℝ)*x*binomialWeight (N-1) x j := by
    have he := Nat.add_one_mul_choose_eq (N-1) j
    rw [hN'] at he
    have heR : (N : ℝ)*((N-1).choose j : ℝ) = (N.choose (j+1) : ℝ)*(j+1) := by exact_mod_cast he
    unfold binomialWeight
    rw [pow_succ]
    push_cast
    linear_combination -(x^j*x)*heR
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero,zero_mul,add_zero]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hs := binomialWeight_sum (N-1) x
  rw [hN'] at hs
  rw [hs]
lemma binomialWeight_mean (N k : ℕ) (hk : 1 ≤ k) (hN : 2*k ≤ N) :
    (∑ j ∈ Finset.range (N+1), (j : ℝ)*binomialWeight N ((k : ℝ)/(N-k : ℕ)) j) =
      (k : ℝ)*(∑ j ∈ Finset.range (N+1), binomialWeight N ((k : ℝ)/(N-k : ℕ)) j) := by
  have hNk : (0 : ℝ) < (N-k : ℕ) := by exact_mod_cast (show 0 < N-k by omega)
  have he : (N : ℝ)*((k : ℝ)/(N-k : ℕ)) = (k : ℝ)*(1+(k : ℝ)/(N-k : ℕ)) := by
    field_simp [hNk.ne']
    rw [Nat.cast_sub (by omega)]
    ring
  rw [binomialWeight_first_moment N (by omega),he,binomialWeight_sum]
  rw [mul_assoc,← pow_succ',show N-1+1=N by omega]
/-- A first-moment finite estimate, with no probability-space infrastructure. -/
lemma firstMoment_peak_bound (N k : ℕ) (hk : 1 ≤ k) (f : ℕ → ℝ)
    (hf : ∀ j, 0 ≤ f j) (hm : ∀ j, f j ≤ f k)
    (hmean : (∑ j ∈ Finset.range (N+1), (j : ℝ)*f j) =
      (k : ℝ)*(∑ j ∈ Finset.range (N+1), f j)) :
    (∑ j ∈ Finset.range (N+1), f j) ≤ 4*((k : ℝ)+1)*f k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hterm : ∀ j ∈ Finset.range (N+1),
      f j ≤ (if j ≤ 2*k then f k else 0)+(j : ℝ)*f j/(2*k) := by
    intro j hj
    by_cases hlow : j ≤ 2*k
    · rw [if_pos hlow]
      exact (hm j).trans (le_add_of_nonneg_right (div_nonneg (mul_nonneg (Nat.cast_nonneg j) (hf j)) (by positivity)))
    · rw [if_neg hlow,zero_add]
      have hjR : 2*(k : ℝ) ≤ j := by exact_mod_cast (show 2*k ≤ j by omega)
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*k)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hjR (hf j)]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib,← Finset.sum_div,hmean] at hsum
  have hcount : (∑ j ∈ Finset.range (N+1), if j ≤ 2*k then f k else 0) ≤
      (2*k+1 : ℕ)*f k := by
    rw [← Finset.sum_filter]
    have hsub : (Finset.range (N+1)).filter (fun j => j ≤ 2*k) ⊆ Finset.range (2*k+1) := by
      intro j hj
      exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj).2; omega)
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_range] at hcard
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hf k)
  have he : (k : ℝ)*(∑ j ∈ Finset.range (N+1), f j)/(2*k) =
      (∑ j ∈ Finset.range (N+1), f j)/2 := by field_simp [hkR.ne']
  rw [he] at hsum
  have hkp : (0 : ℝ) ≤ f k := hf k
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hcount
  nlinarith
lemma binomialWeight_mean_lower (N k : ℕ) (hk : 1 ≤ k) (hN : 2*k ≤ N) :
    (1+(k : ℝ)/(N-k : ℕ))^N ≤ 4*((k : ℝ)+1)*
      (N.choose k : ℝ)*((k : ℝ)/(N-k : ℕ))^k := by
  have hx : 0 ≤ (k : ℝ)/(N-k : ℕ) := by positivity
  have he := firstMoment_peak_bound N k hk (binomialWeight N ((k : ℝ)/(N-k : ℕ)))
    (binomialWeight_nonneg N _ hx) (binomialWeight_mode N k hk hN)
    (binomialWeight_mean N k hk hN)
  rw [binomialWeight_sum] at he
  simpa only [binomialWeight,mul_assoc] using he
end WP
