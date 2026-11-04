import WPFormalization.HigherOrder.CanonicalExpansionProof
/-! Original Theorem 10.2, separated from marked 8.2 so its actual proof can consume 8.2 without a cyclic import. Original full header and label are preserved. -/
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology

/- Theorem 10.2. The Y=0 branch is specified, and continuity/critical extension
are conclusions, not properties silently assigned by the coefficient definition. -/
@[blueprint "thm:canonical-expansion"]
theorem canonical_expansion (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C B c h₀ : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ 0 < h₀ ∧
      GevreyExtension (extractedCoefficient P p) C B ∧
      (∀ j, ContinuousOn (extractedCoefficient P p j) (Set.Icc 0 y₀)) ∧
      (∀ j, extractedCoefficient P p j y₀ = criticalExtractedCoefficient P p j) ∧
      (∀ (g k K : ℕ), h₀ ≤ (complexity g p : ℝ) →
        (K : ℝ) ≤ c*Real.sqrt (complexity g p) →
        let Y := densityY (2*(k : ℝ)/(complexity g p : ℝ))
        |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k -
          ∑ j ∈ Finset.range (K+1), extractedCoefficient P p j Y/
            (complexity g p : ℝ)^j| ≤
          C*B^(K+1)*((K+1).factorial : ℝ)^2/(complexity g p : ℝ)^(K+1)) ∧
      (∃ c' a C' h₁ : ℝ, 0 < c' ∧ c' ≤ c ∧ 0 < a ∧ 0 < C' ∧ 0 < h₁ ∧
        ∀ (g k : ℕ), h₁ ≤ (complexity g p : ℝ) →
          let Y := densityY (2*(k : ℝ)/(complexity g p : ℝ))
          |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k -
            ∑ j ∈ Finset.range (⌊c'*Real.sqrt (complexity g p)⌋₊+1),
              extractedCoefficient P p j Y/(complexity g p : ℝ)^j| ≤
                C'*Real.exp (-a*Real.sqrt (complexity g p))) := by
  exact canonical_expansion_proof P p hp

end WP.HigherOrder
