import WPFormalization.Analysis.ExtractionFactorization

/-! Original extraction-model identity, with its exact parameter domain. -/
noncomputable section
namespace WP

/- Blueprint label(s): eq:CE1
Paper v3: 10.1 [PDF 46]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:CE1"]
theorem extraction_factorization (g p : ℕ) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    markedModel g p Y = markedModel g p 0 *
      Real.exp (complexity g p*extractionS (XR Y))*extractionB p (XR Y) := by
  exact Analysis.extraction_factorization_proof g p Y hY

end WP
