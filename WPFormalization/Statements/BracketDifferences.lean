import WPFormalization.Coefficients.BracketDifferencesProof
noncomputable section
namespace WP

/- Blueprint label(s): eq:C8
Paper v3: 13.8 [PDF 53]
Status: CONDITIONALLY_PROVED; PsiTheory and registered classical inputs remain
-/
@[blueprint "eq:C8"]
theorem bracket_differences (P : PsiTheory) : ∃ C : ℝ, 0 < C ∧
    ∀ g : ℕ, 1 ≤ g →
      bracketB P g 0/volumeModel P g 1 = 1 ∧
      ∀ k : ℕ, k < 3*g-2 →
        0 ≤ bracketB P g k/volumeModel P g 1-bracketB P g (k+1)/volumeModel P g 1 ∧
        bracketB P g k/volumeModel P g 1-bracketB P g (k+1)/volumeModel P g 1 ≤
          C*(k+1)/g := by
  exact bracket_differences_proof P

end WP
