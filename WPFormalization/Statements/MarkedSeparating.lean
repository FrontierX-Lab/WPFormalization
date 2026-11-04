import WPFormalization.Marked.SeparatingProof

/-! Actual separating estimates on the conditional numerical interface. -/
noncomputable section
namespace WP

/- Blueprint label(s): eq:TL19
Paper v3: 6.11 [PDF 32]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL19"]
theorem separating_estimates (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |separatingS P g p Y| ≤ C/(g : ℝ)^2 ∧ |separatingT P g p Y| ≤ C/g := by
  exact separating_estimates_proof P p hp

end WP
