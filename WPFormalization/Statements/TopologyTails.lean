import WPFormalization.Marked.UniformTopologyTails

/-! Lemma C.5: actual topological tails with constants uniform in the marking
count and loss. Each filter bounds both component losses, hence the smaller
component loss, including the one-marking separating sum. -/
noncomputable section
namespace WP

/- In S the component loss is its complexity plus one. -/
@[blueprint "lem:tails"]
def separatingSTail (P : PsiTheory) (g p L : ℕ) (Y : ℝ) : ℝ :=
  markedSplitLossTail P g p 1 L Y

/- In T the component loss is its complexity. -/
@[blueprint "lem:tails"]
def separatingTTail (P : PsiTheory) (g p L : ℕ) (Y : ℝ) : ℝ :=
  markedSplitLossTail P g p 2 L Y

lemma separatingSTail_zero (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (Y : ℝ) :
    separatingSTail P g p 0 Y = separatingS P g p Y := by
  rw [separatingSTail,markedSplitLossTail_zero,
    separatingS_eq_markedSplitConvolution P g p hp]

lemma separatingTTail_zero (P : PsiTheory) (g p : ℕ) (hp : 2 ≤ p) (Y : ℝ) :
    separatingTTail P g p 0 Y = separatingT P g p Y := by
  rw [separatingTTail,markedSplitLossTail_zero,
    separatingT_eq_markedSplitConvolution P g p hp]

@[blueprint "lem:tails"]
theorem topology_tails (P : PsiTheory) (M₀ : ℝ) (hM₀ : 0 < M₀) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∃ H : ℕ,
      (∀ g p : ℕ, 1 ≤ p → H ≤ complexity g p →
        (p : ℝ) ≤ M₀*Real.sqrt (complexity g p : ℝ) →
        ∀ L : ℕ, 2 ≤ L → (L : ℝ) ≤ Real.sqrt (complexity g p : ℝ) →
        ∀ Y ∈ Set.Icc 0 y₀,
          separatingSTail P g p L Y ≤ C*(B*((p : ℝ)+L)/(complexity g p : ℝ))^L) ∧
      (∀ g p : ℕ, 2 ≤ p → H ≤ complexity g p →
        (p : ℝ) ≤ M₀*Real.sqrt (complexity g p : ℝ) →
        ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ Real.sqrt (complexity g p : ℝ) →
        ∀ Y ∈ Set.Icc 0 y₀,
          separatingTTail P g p L Y ≤ C*(B*((p : ℝ)+L)/(complexity g p : ℝ))^L) := by
  exact uniform_topology_tails_proof P M₀ hM₀

end WP
