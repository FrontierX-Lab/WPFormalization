import WPFormalization.Marked.FirstDegreeProof

/-! The original first degree estimate and the stronger all-degree remainder
used in the genuine dilaton summation. The original range is preserved. -/
noncomputable section
namespace WP

/- Blueprint label(s): lem:first-degree
Paper v3: 7.2 [PDF 35]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:first-degree"]
theorem first_degree (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ d : List ℕ, d.length = p →
    (d.sum : ℝ) ≤ Real.rpow (complexity g p) (1/4 : ℝ) →
    ∀ Y ∈ Set.Icc 0 y₀,
      |profile P g d Y - (1-degreeCorrection d Y/complexity g p)| ≤
        C*(d.sum+1 : ℝ)^4/(complexity g p : ℝ)^2 := by
  exact first_degree_proof P p hp

@[blueprint "lem:first-degree"]
theorem first_degree_all_degrees (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ d : List ℕ, d.length = p →
    ∀ Y ∈ Set.Icc 0 y₀,
      |profile P g d Y - (1-degreeCorrection d Y/complexity g p)| ≤
        C*(d.sum+1 : ℝ)^4/(complexity g p : ℝ)^2 := by
  exact first_degree_all_degrees_proof P p hp

end WP
