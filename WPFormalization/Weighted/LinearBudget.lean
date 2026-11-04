import Mathlib
/-! A uniform finite budget for inactive-merger savings versus at most four
exceptional birth pairs in the weighted linear recursion. The tuning interval
0 < c ≤ 1/64 makes the quadratic birth coefficient absorbable. The final
finite_label_savings lemma keeps the actual favorable-label count explicit. -/
noncomputable section
namespace WP
def inactiveMergeRatio (c : ℝ) (I : ℕ) : ℝ := max (1/4) (1/max 1 (c*Real.sqrt I))
lemma inactiveMergeRatio_le_one (c : ℝ) (I : ℕ) : inactiveMergeRatio c I ≤ 1 := by
  unfold inactiveMergeRatio
  apply max_le (by norm_num)
  apply (div_le_one (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _))).mpr
  exact le_max_left _ _
lemma weighted_linear_birth_budget (c : ℝ) (hc : 0 < c) (hsmall : c ≤ 1/64) (I : ℕ) :
    128*(1+c*Real.sqrt (I+2))^2 -
      (1-inactiveMergeRatio c I)*(I-1 : ℕ) ≤ 2048 := by
  have hc₂ : c^2 ≤ (1/4096 : ℝ) := by nlinarith
  have ht₁ := inactiveMergeRatio_le_one c I
  have hSq : (Real.sqrt (I : ℝ))^2 = (I : ℝ) := Real.sq_sqrt (by positivity)
  have hSq₂ : (Real.sqrt ((I : ℝ)+2))^2 = (I : ℝ)+2 := Real.sq_sqrt (by positivity)
  have hy₀ : (0 : ℝ) ≤ c*Real.sqrt (I+2) := by positivity
  have hy₂ : (c*Real.sqrt (I+2))^2 = c^2*((I : ℝ)+2) := by rw [mul_pow,hSq₂]
  by_cases hI : c*Real.sqrt (I : ℝ) ≤ 2
  · have hx₀ : (0 : ℝ) ≤ c*Real.sqrt I := by positivity
    have hx₂ : (c*Real.sqrt (I : ℝ))^2 ≤ 4 := by nlinarith
    rw [mul_pow,hSq] at hx₂
    have hy : c*Real.sqrt (I+2) ≤ 3 := by nlinarith [hy₂]
    have hpen : 0 ≤ (1-inactiveMergeRatio c I)*(I-1 : ℕ) := by positivity
    nlinarith
  · have hI' : 2 < c*Real.sqrt (I : ℝ) := by linarith
    have hIp : 1 ≤ I := by
      by_contra h
      have h0 : I=0 := by omega
      rw [h0] at hI'
      norm_num at hI'
    have hcast : ((I-1 : ℕ) : ℝ) = (I : ℝ)-1 := by rw [Nat.cast_sub hIp]; norm_num
    have ht : inactiveMergeRatio c I ≤ 1/2 := by
      unfold inactiveMergeRatio
      rw [max_eq_right (by linarith : 1 ≤ c*Real.sqrt I)]
      apply max_le (by norm_num)
      exact (div_le_iff₀ (by linarith : 0 < c*Real.sqrt I)).mpr (by linarith)
    have hpen : (I-1 : ℕ)*(1/2 : ℝ) ≤ (1-inactiveMergeRatio c I)*(I-1 : ℕ) := by
      have he := mul_le_mul_of_nonneg_right (show (1/2 : ℝ) ≤ 1-inactiveMergeRatio c I by linarith)
        (show (0 : ℝ) ≤ (I-1 : ℕ) by positivity)
      nlinarith [he]
    have hyYoung := sq_nonneg (Real.sqrt ((I : ℝ)+2)-1024*c)
    have hcross : 256*c*Real.sqrt (I+2) ≤ ((I : ℝ)+2)/8+32 := by nlinarith [hyYoung,hSq₂]
    have hprod := mul_le_mul_of_nonneg_right hc₂ (show (0 : ℝ) ≤ (I : ℝ)+2 by positivity)
    rw [hcast] at hpen
    nlinarith [hy₂]
lemma finite_label_savings {α : Type*} [DecidableEq α] (s t : Finset α) (ht : t ⊆ s)
    (w f : α → ℝ) (r : ℝ) (hr : r ≤ 1)
    (hw : ∀ i ∈ s, 1 ≤ w i) (hf : ∀ i ∈ s, f i ≤ 1)
    (htf : ∀ i ∈ t, f i ≤ r) :
    (∑ i ∈ s, w i*f i) ≤ (∑ i ∈ s, w i)-(1-r)*t.card := by
  have hp : ∀ i ∈ s, w i*f i ≤ w i-(if i∈t then 1-r else 0) := by
    intro i hi
    by_cases hit : i∈t
    · rw [if_pos hit]
      have he := mul_le_mul_of_nonneg_left (htf i hit) (le_trans (by norm_num) (hw i hi))
      have hsave := mul_nonneg (show 0 ≤ w i-1 by linarith [hw i hi]) (show 0 ≤ 1-r by linarith)
      nlinarith
    · rw [if_neg hit,sub_zero]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf i hi) (le_trans (by norm_num) (hw i hi))
  have hs := Finset.sum_le_sum hp
  rw [Finset.sum_sub_distrib] at hs
  have he : (∑ i ∈ s, if i∈t then 1-r else 0) = (1-r)*t.card := by
    rw [← Finset.sum_filter]
    have hfilt : s.filter (fun i => i∈t) = t := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨ht h,h⟩
    rw [hfilt,Finset.sum_const,nsmul_eq_mul]
    ring
  rw [he] at hs
  exact hs
end WP
