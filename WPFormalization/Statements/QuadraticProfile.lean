import WPFormalization.Marked.QuadraticProfile

/-! Original quadratic profile estimate on the conditional numerical interface. -/
noncomputable section
namespace WP

/- Blueprint label(s): eq:TL23
Paper v3: 6.15 [PDF 33]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL23"]
theorem quadratic_profile (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ d : List ℕ, d.length = p →
    ∀ Y ∈ Set.Icc 0 y₀, 0 ≤ 1-profile P g d Y ∧
      1-profile P g d Y ≤ C*(d.sum : ℝ)*(d.sum+1)/g := by
  exact quadratic_profile_proof P p hp

end WP
