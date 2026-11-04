import WPFormalization.Coefficients.LogarithmicComparisonProof
noncomputable section
namespace WP
open Filter
open scoped Topology

/- Lemma E.3, all degree endpoints included. -/
/- Blueprint label(s): lem:log-comparison
Paper v3: E.3 [PDF 98]
Status: CONDITIONALLY_PROVED; PsiTheory and seven registered classical roots remain
-/
@[blueprint "lem:log-comparison"]
theorem logarithmic_comparison (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ k : ℕ, k ≤ 3*g-2 →
      |logComparisonG P g k-(g : ℝ)*logDegreeProfile ((k : ℝ)/g)| ≤ C*Real.sqrt g := by
  exact logarithmic_comparison_proof P

end WP
