import WPFormalization.Marked.CriticalAnchor

/-! Original absolute marked prefactor, uniform on the full half-open interval. -/
noncomputable section
namespace WP

/- Proposition 7.1, fixed markings, uniform in the full half-open parameter interval. -/
/- Blueprint label(s): prop:prefactor
Paper v3: 7.1 [PDF 35]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "prop:prefactor"]
theorem absolute_prefactor (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Ico 0 y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y-1| ≤ C*Real.log (g+1)/g := by
  exact absolute_prefactor_proof P p hp

end WP
