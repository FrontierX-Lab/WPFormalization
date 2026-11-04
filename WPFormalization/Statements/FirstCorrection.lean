import WPFormalization.Volumes.FirstCorrectionProof

/-! Theorem 8.1 with its original canonical finite integral and uniform error. -/
noncomputable section
namespace WP.HigherOrder

/- Theorem 8.1, with the finite gamma_p integral of Eq.8.1. -/
@[blueprint "thm:first-correction"]
theorem first_correction (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Ico 0 y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y -
        (1+firstMarkedCorrection p Y/(complexity g p : ℝ))| ≤
      C*Real.log (g+1)/(g : ℝ)^2 := by
  exact first_correction_proof P p hp

end WP.HigherOrder
