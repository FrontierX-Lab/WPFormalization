import WPFormalization.Volumes.SharpExtractionProof

/-! Original Theorem 10.1, separated from volume definitions to permit the proved canonical extraction theorem as an input without an import cycle. -/
noncomputable section
namespace WP

/- Blueprint label(s): thm:sharp-extraction
Paper v3: 10.1 [PDF 47]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "thm:sharp-extraction"]
theorem sharp_extraction (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ,
      |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k-1| ≤ C/complexity g p := by
  exact sharp_extraction_proof P p hp

end WP
