import WPFormalization.Coefficients.AdjacentLimitProof
noncomputable section
namespace WP
open Filter
open scoped Topology

/- Theorem 1.4 (the quantitative clauses are included by association to E.1). -/
/- Blueprint label(s): thm:coefficient
Paper v3: 1.4 [PDF 8]
Status: CONDITIONALLY_PROVED; registered classical inputs remain
-/
@[blueprint "thm:coefficient"]
theorem adjacent_limit (P : PsiTheory) :
    ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ, k < 3*g-2 →
      adjacentError P g k ≤ ε := by
  exact adjacent_limit_proof P

end WP
