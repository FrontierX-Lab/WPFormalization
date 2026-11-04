import WPFormalization.Coefficients.QuantitativeAdjacentProof
noncomputable section
namespace WP
open Filter
open scoped Topology

/- Theorem E.1, both exponents and quantifier dependence retained. -/
/- Blueprint label(s): thm:coefficient, thm:quantitative-coefficient
Paper v3: 1.4 [PDF 8]; E.1 [PDF 97]
Status: CONDITIONALLY_PROVED; registered classical inputs remain
-/
@[blueprint "thm:coefficient", blueprint "thm:quantitative-coefficient"]
theorem quantitative_adjacent (P : PsiTheory) :
    (∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ, k < 3*g-2 →
      adjacentError P g k ≤ C*Real.rpow g (-1/8 : ℝ)) ∧
    (∀ ε ∈ Set.Ioo (0 : ℝ) 3, ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      ∀ k : ℕ, ε*g ≤ k → k < 3*g-2 → adjacentError P g k ≤ C*Real.rpow g (-1/4 : ℝ)) := by
  exact quantitative_adjacent_proof P

end WP
