import WPFormalization.Marked.GenusRatio

/-! Original marked ratio statement, proved on the conditional numerical interface. -/
noncomputable section
namespace WP

/- Blueprint label(s): eq:TL27
Paper v3: 6.19 [PDF 34]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL27"]
theorem marked_genus (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |W P (g-1) (p+2) Y / W P g p Y - 1| ≤ C/g := by
  exact marked_genus_proof P p hp

end WP
