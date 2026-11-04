import Mathlib
/-! A finite strict-loss convolution with nonnegative errors collapses to one geometric convolution. The original minimum loss a is retained, and every resulting error order is L-k with k>=a. The forcing part has the same exponential base. This numerical lemma has no asymptotic, recurrence, or hierarchy assumption. -/
noncomputable section
namespace WP.HigherOrder
lemma finite_strict_loss_geometric_convolution (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (a L : ℕ) (E : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q) :
    (∑ r ∈ Finset.range L, if a ≤ r then A ^ r *
      ((∑ i ∈ Finset.range (L - r), B ^ i * E (L - r - i)) + B ^ (L - r)) else 0) ≤
    (∑ k ∈ Finset.range L, if a ≤ k then (2 * max A B) ^ k * E (L - k) else 0) +
      (2 * max A B) ^ L := by
  let R := max A B
  have hR : 0 ≤ R := hA.trans (le_max_left _ _)
  have hpow (r i : ℕ) : A ^ r * B ^ i ≤ R ^ (r + i) := by
    rw [pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hA (le_max_left _ _) _) (pow_le_pow_left₀ hB (le_max_right _ _) _)
      (pow_nonneg hB _) (pow_nonneg hR _)
  have hsplit : (∑ r ∈ Finset.range L, if a ≤ r then A ^ r *
      ((∑ i ∈ Finset.range (L - r), B ^ i * E (L - r - i)) + B ^ (L - r)) else 0) =
      (∑ r ∈ Finset.range L, ∑ i ∈ Finset.range (L - r),
        if a ≤ r then A ^ r * B ^ i * E (L - r - i) else 0) +
      ∑ r ∈ Finset.range L, if a ≤ r then A ^ r * B ^ (L - r) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases ha : a ≤ r
    · simp only [ite_eq_left ha, mul_add, Finset.mul_sum, mul_assoc]
    · simp only [ite_eq_right ha, Finset.sum_const_zero, zero_add]
  rw [hsplit]
  apply add_le_add
  · rw [← Finset.sum_range_diag_flip L (fun r i => if a ≤ r then A ^ r * B ^ i * E (L - r - i) else 0)]
    apply Finset.sum_le_sum
    intro k hk
    by_cases hak : a ≤ k
    · rw [ite_eq_left hak]
      have hterm (r : ℕ) (hr : r ∈ Finset.range (k + 1)) :
          (if a ≤ r then A ^ r * B ^ (k - r) * E (L - r - (k - r)) else 0) ≤
            R ^ k * E (L - k) := by
        have hrk : r ≤ k := by have ht := Finset.mem_range.mp hr; omega
        by_cases har : a ≤ r
        · rw [ite_eq_left har, show L - r - (k - r) = L - k by omega]
          have hp := hpow r (k - r)
          rw [Nat.add_sub_of_le hrk] at hp
          exact mul_le_mul_of_nonneg_right hp (hE _)
        · rw [ite_eq_right har]
          exact mul_nonneg (pow_nonneg hR _) (hE _)
      calc
        _ ≤ ∑ r ∈ Finset.range (k + 1), R ^ k * E (L - k) := Finset.sum_le_sum hterm
        _ = ((k + 1 : ℕ) : ℝ) * (R ^ k * E (L - k)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ k * (R ^ k * E (L - k)) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast k.lt_two_pow_self.succ_le) (mul_nonneg (pow_nonneg hR _) (hE _))
        _ = _ := by dsimp [R]; rw [mul_pow]; ring
    · rw [ite_eq_right hak]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro r hr
      rw [ite_eq_right (by have ht := Finset.mem_range.mp hr; omega : ¬ a ≤ r)]
  · have hterm (r : ℕ) (hr : r ∈ Finset.range L) :
        (if a ≤ r then A ^ r * B ^ (L - r) else 0) ≤ R ^ L := by
      by_cases har : a ≤ r
      · rw [ite_eq_left har]
        have hp := hpow r (L - r)
        rwa [Nat.add_sub_of_le (Finset.mem_range.mp hr).le] at hp
      · rw [ite_eq_right har]
        positivity
    calc
      _ ≤ ∑ r ∈ Finset.range L, R ^ L := Finset.sum_le_sum hterm
      _ = (L : ℝ) * R ^ L := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ L * R ^ L :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast L.lt_two_pow_self.le) (pow_nonneg hR _)
      _ = _ := by rw [← mul_pow]
end WP.HigherOrder
