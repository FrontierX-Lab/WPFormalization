import WPFormalization.Marked.VolumeRatios
import WPFormalization.Statements.StringFlow

/-! Original fixed-marking ratio proposition, using the proved string flow. -/
noncomputable section
namespace WP

/- Proposition 6.2, with the p=0 genus-exchange extension separately quantified. -/
/- Blueprint label(s): prop:marked-ratios
Paper v3: 6.2 [PDF 34]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "prop:marked-ratios"]
theorem marked_ratios (P : PsiTheory) :
    (∀ p : ℕ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      ∀ Y ∈ Set.Ico 0 y₀,
        |XR Y*markedF P g (p+1) (XR Y)/markedF P g p (XR Y) -
          (complexity g p : ℝ)*Psi (XR Y)| ≤ C*Psi (XR Y)) ∧
    (∀ p : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Ico 0 y₀,
      |markedF P (g-1) (p+2) (XR Y)/(4*r Y*markedF P g p (XR Y))-1| ≤ C/g) := by
  exact marked_ratios_of_shift_flow P (fun g p hs Y hY => string_flow P g p hs Y hY)

end WP
