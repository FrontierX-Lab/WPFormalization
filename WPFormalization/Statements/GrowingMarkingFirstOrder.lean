import WPFormalization.Marked.GrowingFirstOrder

/-! Original Lemma C.6: all degrees and growing marking counts with uniform constants. -/
noncomputable section
namespace WP

@[blueprint "lem:first-order"]
theorem growing_marking_first_order (P : PsiTheory) (M₀ : ℝ) (hM : 0 < M₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ h₀ : ℕ, ∀ g p : ℕ, 1 ≤ p →
    h₀ ≤ complexity g p → (p : ℝ) ≤ M₀*Real.sqrt (complexity g p) →
    ∀ Y ∈ Set.Icc 0 y₀,
      (∀ d : List ℕ, d.length = p →
        0 ≤ 1-profile P g d Y ∧ 1-profile P g d Y ≤
          min 1 (C*(d.sum : ℝ)*(d.sum+p+1)/complexity g p)) ∧
      |cuspCorrection P g p Y-1|+|genusCorrection P g p Y-1| ≤ C*(p+1)/complexity g p := by
  exact growing_marking_first_order_proof P M₀ hM

end WP
