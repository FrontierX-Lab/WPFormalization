import WPFormalization.HigherOrder.DescentRemainderStep
/-! The final one-marking scalar row of the local C.3 induction. The current cusp error at order L is separated exactly from the strict previous-order cusp convolution. The current two-marking genus uses its actual own complexity h+1, while the cusp at (g-1,3) has exactly parent complexity h. Constants precede all states and orders; no new error estimate or full C.3 target is assumed. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma actual_genus_one_uniform_scalar_row (P : PsiTheory) :
    ∃ D B δ₀ : ℝ, ∃ M₀ : ℕ, 0 < D ∧ 0 < B ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 2 ≤ M₀ ∧
      ∀ M : ℕ, M₀ ≤ M → ∀ g L : ℕ, 2 ≤ g → 1 ≤ L →
      ∀ Y ∈ Icc (0 : ℝ) y₀,
      scalarOrderWeight (M : ℝ) L 1 ^ 2 / (complexity g 1 : ℝ) < δ₀ →
      ∀ H C : ℝ, 0 ≤ H → 0 ≤ C → ∀ EC : ℕ → ℝ, (∀ q, 0 ≤ EC q) →
      (|genusCorrection P g 2 Y - truncationValue (formalGenus P Y 2) L (1 / (complexity g 2 : ℝ))| ≤
        H * scalarOrderWeight (M : ℝ) L 2 ^ (2 * L) / (complexity g 2 : ℝ) ^ L) →
      (∀ g' p' : ℕ, 1 ≤ p' → Stable g' p' →
        |cuspCorrection P g' p' Y - truncationValue (formalCusp P Y p') L (1 / (complexity g' p' : ℝ))| ≤
          C * scalarOrderWeight (M : ℝ) L p' ^ (2 * L) / (complexity g' p' : ℝ) ^ L) →
      (∀ g' p' q : ℕ, 1 ≤ p' → Stable g' p' → 1 ≤ q → q < L →
        |cuspCorrection P g' p' Y - truncationValue (formalCusp P Y p') q (1 / (complexity g' p' : ℝ))| ≤
          EC q * scalarOrderWeight (M : ℝ) q p' ^ (2 * q) / (complexity g' p' : ℝ) ^ q) →
      |genusCorrection P g 1 Y - truncationValue (formalGenus P Y 1) L (1 / (complexity g 1 : ℝ))| ≤
        D * (H + C + (∑ i ∈ Finset.range L, if 1 ≤ i then B ^ i * EC (L - i) else 0) + B ^ L) *
          scalarOrderWeight (M : ℝ) L 1 ^ (2 * L) / (complexity g 1 : ℝ) ^ L := by
  obtain ⟨D, B, M₀, δ₀, hD, hB, hM₀, hδ₀, hδ₀1, hstep⟩ := actual_genus_one_uniform_remainder_step P
  let N₀ : ℕ := max 2 ⌈M₀⌉₊
  have hN₀ : 2 ≤ N₀ := le_max_left _ _
  refine ⟨D, B, δ₀, N₀, hD, hB, hδ₀, hδ₀1, hN₀, ?_⟩
  intro M hM g L hg hL Y hY hsmall H C hH hC EC hEC hgenus hcurrent hold
  have hMreal : M₀ ≤ (M : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 2 ⌈M₀⌉₊).trans hM)
  let E : ℕ → ℝ := fun q => if q = L then C else EC q
  have hE : ∀ q, 0 ≤ E q := by
    intro q
    dsimp [E]
    split_ifs
    · exact hC
    · exact hEC q
  have hs1 : Stable g 1 := by unfold Stable; omega
  have hs3 : Stable (g - 1) 3 := by unfold Stable; omega
  have hcomplex : complexity (g - 1) 3 = complexity g 1 := by unfold complexity; omega
  have hcusps (q : ℕ) (hq : 1 ≤ q) (hql : q ≤ L) :
      |cuspCorrection P g 1 Y - truncationValue (formalCusp P Y 1) q (1 / (complexity g 1 : ℝ))| ≤
          E q * scalarOrderWeight (M : ℝ) q 1 ^ (2 * q) / (complexity g 1 : ℝ) ^ q ∧
      |cuspCorrection P (g - 1) 3 Y - truncationValue (formalCusp P Y 3) q (1 / (complexity g 1 : ℝ))| ≤
          E q * scalarOrderWeight (M : ℝ) q 3 ^ (2 * q) / (complexity g 1 : ℝ) ^ q := by
    by_cases he : q = L
    · subst q
      dsimp only [E]
      rw [ite_eq_left rfl]
      exact ⟨hcurrent g 1 (by omega) hs1, by simpa only [hcomplex] using hcurrent (g - 1) 3 (by omega) hs3⟩
    · have hqL : q < L := lt_of_le_of_ne hql he
      dsimp only [E]
      rw [ite_eq_right he]
      exact ⟨hold g 1 q (by omega) hs1 hq hqL, by simpa only [hcomplex] using hold (g - 1) 3 q (by omega) hs3 hq hqL⟩
  have he := hstep (M : ℝ) hMreal g L hg hL Y hY hsmall H hH E hE hgenus hcusps
  have hsplit : (∑ i ∈ Finset.range L, B ^ i * E (L - i)) =
      C + ∑ i ∈ Finset.range L, if 1 ≤ i then B ^ i * EC (L - i) else 0 := by
    have hpoint (i : ℕ) (hi : i ∈ Finset.range L) :
        B ^ i * E (L - i) = (if i = 0 then C else 0) +
          (if 1 ≤ i then B ^ i * EC (L - i) else 0) := by
      by_cases hzero : i = 0
      · subst i
        simp [E]
      · have hiL : i < L := Finset.mem_range.mp hi
        have hne : L - i ≠ L := by omega
        simp only [E, ite_eq_right hne, ite_eq_right hzero, ite_eq_left (by omega : 1 ≤ i), zero_add]
    calc
      _ = ∑ i ∈ Finset.range L, ((if i = 0 then C else 0) +
          (if 1 ≤ i then B ^ i * EC (L - i) else 0)) := Finset.sum_congr rfl hpoint
      _ = _ := by rw [Finset.sum_add_distrib]; simp [show L ≠ 0 by omega]
  rw [hsplit] at he
  convert he using 1 <;> ring
end WP.HigherOrder
