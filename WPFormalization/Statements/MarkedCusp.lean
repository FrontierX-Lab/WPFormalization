import WPFormalization.Marked.CuspPositive

/-! Original marked ratio statement, proved on the conditional numerical interface. -/
noncomputable section
namespace WP

/- Blueprint label(s): eq:TL24
Paper v3: 6.16 [PDF 33]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL24"]
theorem marked_cusp (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |(complexity g p : ℝ)*W P g p Y/W P g (p+1) Y - A Y| ≤ C/g := by
  exact marked_cusp_proof P p hp

end WP
