import WPFormalization.HigherOrder.ScalarRemainderPairing
import WPFormalization.HigherOrder.SmallComponentCounts
import WPFormalization.HigherOrder.FiniteLossMajorant
import WPFormalization.Marked.UniformComplexityGrowth
/-! The actual small KdV component and finite loss count. The genuine all-marking Gamma growth supplies its binomial label bound. The finite low-loss remainder is controlled by a strictly previous-order ratio-error sequence; the loss r>=1 is retained. The ratio-error estimate is an explicit supporting input here, not an assumed completed C.3 result. -/
noncomputable section
namespace WP.HigherOrder
open Set

lemma kdv_small_component_label_bound (P : PsiTheory) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ p j s : ℕ, 2 ≤ p → Stable j (s + 2) → 1 ≤ 2 * j + s →
      ∀ S : ℝ, ((p - 2 + (2 * j + s) : ℕ) : ℝ) ≤ S → ∀ Y ∈ Icc (0 : ℝ) y₀,
      |(Nat.choose (p - 2) s : ℝ) * W P j (s + 2) Y| ≤ (T * S) ^ (2 * j + s) := by
  obtain ⟨T, hT, hW⟩ := W_uniform_complexity_exponential P
  refine ⟨T, hT, ?_⟩
  intro p j s hp hs hr S hS Y hY
  have hc : complexity j (s + 2) = 2 * j + s := by unfold complexity; omega
  have hW0 : 0 ≤ W P j (s + 2) Y := W_nonneg P j (s + 2) (by omega) Y hY
  have hbound := hW j (s + 2) hs Y hY
  rw [hc] at hbound
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hW0]
  have hG : 0 ≤ Real.Gamma ((2 * j + s : ℕ) : ℝ) :=
    (Real.Gamma_pos_of_pos (by exact_mod_cast (show 0 < 2 * j + s by omega))).le
  have hS0 : 0 ≤ S := (Nat.cast_nonneg _).trans hS
  calc
    _ ≤ (Nat.choose (p - 2) s : ℝ) * (Real.Gamma ((2 * j + s : ℕ) : ℝ) * T ^ (2 * j + s)) :=
      mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = ((Nat.choose (p - 2) s : ℝ) * Real.Gamma ((2 * j + s : ℕ) : ℝ)) * T ^ (2 * j + s) := by ring
    _ ≤ ((p - 2 + (2 * j + s) : ℕ) : ℝ) ^ (2 * j + s) * T ^ (2 * j + s) :=
      mul_le_mul_of_nonneg_right (choose_gamma_le_add_pow (p - 2) (2 * j + s) s hr (by omega))
        (pow_nonneg (by linarith) _)
    _ ≤ S ^ (2 * j + s) * T ^ (2 * j + s) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hS _) (pow_nonneg (by linarith) _)
    _ = _ := by rw [mul_pow]; ring

lemma low_loss_rectangular_sum_bound (L n : ℕ) (hL : 1 ≤ L) (F : ℕ → ℝ)
    (hF : ∀ r, 0 ≤ F r) :
    (∑ j ∈ Finset.range L, ∑ s ∈ Finset.range n,
      if 1 ≤ 2 * j + s ∧ 2 * j + s < L then F (2 * j + s) else 0) ≤
    ∑ r ∈ Finset.range L, if 1 ≤ r then (2 : ℝ) ^ r * F r else 0 := by
  have hcrop (j : ℕ) :
      (∑ s ∈ Finset.range n, if 1 ≤ 2 * j + s ∧ 2 * j + s < L then F (2 * j + s) else 0) ≤
      ∑ s ∈ Finset.range L, if 1 ≤ 2 * j + s ∧ 2 * j + s < L then F (2 * j + s) else 0 := by
    by_cases hn : n ≤ L
    · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      intro s hs hnot
      split_ifs
      · exact hF _
      · exact le_rfl
    · apply le_of_eq
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : L ≤ n))
      intro s hs hnot
      have hsL : L ≤ s := by simpa only [Finset.mem_range, not_lt] using hnot
      rw [ite_eq_right (by omega : ¬ (1 ≤ 2 * j + s ∧ 2 * j + s < L))]
  apply (Finset.sum_le_sum (fun j hj => hcrop j)).trans
  have he : L - 1 + 1 = L := by omega
  have hf := loss_pair_count_bound 1 (L - 1) F hF
  simpa only [he, show ∀ j s : ℕ, (1 ≤ 2 * j + s ∧ 2 * j + s ≤ L - 1) ↔
    (1 ≤ 2 * j + s ∧ 2 * j + s < L) from fun j s => by omega] using hf

lemma kdv_low_mass_remainder_scaled_bound (P : PsiTheory) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ g p L : ℕ, 2 ≤ p → 1 ≤ L → ∀ Y ∈ Icc (0 : ℝ) y₀,
      ∀ S h D : ℝ, 1 ≤ S → 0 < h → 0 ≤ D →
      ((p : ℝ) + L ≤ S) → ∀ E : ℕ → ℝ, (∀ q, 0 ≤ E q) →
      (∀ j ∈ Finset.range L, ∀ s ∈ Finset.range (p - 1),
        Stable j (s + 2) → 1 ≤ 2 * j + s → 2 * j + s < L →
        |W P (g - j) (p - s) Y / W P g p Y -
          truncationValue (ratioSeries Y (formalHierarchyJet P Y) p j s) L (1 / h)| ≤
          D ^ (2 * j + s) * S ^ (2 * (L - (2 * j + s))) / h ^ L * E (L - (2 * j + s))) →
      |kdvActualLowMass P g p L Y - truncationValue (kdvFormalLowSeries P Y p L) L (1 / h)| ≤
        S ^ (2 * L) / h ^ L *
          ∑ r ∈ Finset.range L, if 1 ≤ r then (2 * T * D) ^ r * E (L - r) else 0 := by
  obtain ⟨T, hT, hlabel⟩ := kdv_small_component_label_bound P
  refine ⟨T, hT, ?_⟩
  intro g p L hp hL Y hY S h D hS hh hD hSp E hE hratio
  rw [kdv_low_remainder_pairing]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hS0 : 0 ≤ S := by linarith
  have hT0 : 0 ≤ T := by linarith
  let F : ℕ → ℝ := fun r => (T * D) ^ r * E (L - r)
  have hF : ∀ r, 0 ≤ F r := fun r => mul_nonneg (pow_nonneg (mul_nonneg hT0 hD) _) (hE _)
  have hpoint (j : ℕ) (hj : j ∈ Finset.range L) (s : ℕ) (hs : s ∈ Finset.range (p - 1)) :
      |if Stable j (s + 2) ∧ 1 ≤ 2 * j + s ∧ 2 * j + s < L then
        (Nat.choose (p - 2) s : ℝ) * W P j (s + 2) Y *
          (W P (g - j) (p - s) Y / W P g p Y -
            truncationValue (ratioSeries Y (formalHierarchyJet P Y) p j s) L (1 / h)) else 0| ≤
      (S ^ (2 * L) / h ^ L) *
        (if 1 ≤ 2 * j + s ∧ 2 * j + s < L then F (2 * j + s) else 0) := by
    by_cases ht : Stable j (s + 2) ∧ 1 ≤ 2 * j + s ∧ 2 * j + s < L
    · have hmask : 1 ≤ 2 * j + s ∧ 2 * j + s < L := ⟨ht.2.1, ht.2.2⟩
      rw [ite_eq_left ht, ite_eq_left hmask, abs_mul]
      have hsP : ((p - 2 + (2 * j + s) : ℕ) : ℝ) ≤ S := by
        have hn : p - 2 + (2 * j + s) ≤ p + L := by omega
        exact (show ((p - 2 + (2 * j + s) : ℕ) : ℝ) ≤ (p : ℝ) + L by exact_mod_cast hn).trans hSp
      have hb := hlabel p j s hp ht.1 ht.2.1 S hsP Y hY
      have he := hratio j hj s hs ht.1 ht.2.1 ht.2.2
      have hmul := mul_le_mul hb he (abs_nonneg _) (by positivity : 0 ≤ (T * S) ^ (2 * j + s))
      apply hmul.trans
      let r := 2 * j + s
      have hr : r ≤ L := ht.2.2.le
      have hSr : S ^ r * S ^ (2 * (L - r)) ≤ S ^ (2 * L) := by
        rw [← pow_add]
        apply pow_le_pow_right₀ hS
        omega
      calc
        _ = ((T * D) ^ r * E (L - r)) * (S ^ r * S ^ (2 * (L - r))) / h ^ L := by dsimp [r]; rw [mul_pow, mul_pow]; ring
        _ ≤ ((T * D) ^ r * E (L - r)) * S ^ (2 * L) / h ^ L :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSr (hF r)) (pow_nonneg hh.le _)
        _ = _ := by dsimp [F, r]; ring
    · rw [ite_eq_right ht, abs_zero]
      apply mul_nonneg (by positivity)
      split_ifs
      · exact hF _
      · exact le_rfl
  calc
    _ ≤ ∑ j ∈ Finset.range L, ∑ s ∈ Finset.range (p - 1),
        (S ^ (2 * L) / h ^ L) * (if 1 ≤ 2 * j + s ∧ 2 * j + s < L then F (2 * j + s) else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun s hs => hpoint j hj s hs)
    _ = (S ^ (2 * L) / h ^ L) *
        ∑ j ∈ Finset.range L, ∑ s ∈ Finset.range (p - 1),
          if 1 ≤ 2 * j + s ∧ 2 * j + s < L then F (2 * j + s) else 0 := by
      simp_rw [← Finset.mul_sum]
    _ ≤ (S ^ (2 * L) / h ^ L) *
        ∑ r ∈ Finset.range L, if 1 ≤ r then (2 : ℝ) ^ r * F r else 0 :=
      mul_le_mul_of_nonneg_left (low_loss_rectangular_sum_bound L (p - 1) hL F hF) (by positivity)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      split_ifs
      · dsimp [F]
        simp only [mul_pow]
        ring
      · rfl
end WP.HigherOrder
