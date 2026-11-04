import WPFormalization.Volumes.TransportProof

/-! Original quantitative transport equation on the full half-open parameter interval. -/
noncomputable section
namespace WP

/- Blueprint label(s): eq:PF8
Paper v3: 7.8 [PDF 36]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:PF8"]
theorem transport_equation (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Ico 0 y₀,
      |A Y*r Y*deriv (fun t => Real.log (markedF P g p (XR t))) Y -
        ((complexity g p : ℝ)+transportBeta p Y)| ≤ C/complexity g p := by
  exact transport_equation_proof P p hp

end WP
