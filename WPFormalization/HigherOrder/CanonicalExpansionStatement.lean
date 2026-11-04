import WPFormalization.HigherOrder.Extraction
import WPFormalization.HigherOrder.ExtensionDefinitions
import WPFormalization.HigherOrder.MarkedExpansionProof
/-! Original marked Theorem 8.2. Canonical 10.2 is in CanonicalExtractionStatement
so its proof may consume the marked theorem without a cyclic dependency. -/
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology

/- Theorem 8.2. All constants precede genus, truncation and Y; the real estimate,
logarithmic estimate, common complex neighborhood and optimal truncation are kept. -/
@[blueprint "thm:full-expansion"]
theorem full_expansion (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C B c h₀ : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ 0 < h₀ ∧
      GevreyExtensionPair (logarithmicMarkedCoefficient P p) (markedCoefficient P p) C B ∧
      (∀ (g K : ℕ), h₀ ≤ (complexity g p : ℝ) →
        (K : ℝ) ≤ c*Real.sqrt (complexity g p) → ∀ Y ∈ Set.Ico 0 y₀,
        |Real.pi*markedF P g p (XR Y)/markedModel g p Y -
          ∑ j ∈ Finset.range (K+1), markedCoefficient P p j Y/(complexity g p : ℝ)^j| ≤
            C*B^(K+1)*((K+1).factorial : ℝ)^2/(complexity g p : ℝ)^(K+1)) ∧
      (∀ (g K : ℕ), h₀ ≤ (complexity g p : ℝ) →
        (K : ℝ) ≤ c*Real.sqrt (complexity g p) → ∀ Y ∈ Set.Ico 0 y₀,
        |Real.log (Real.pi*markedF P g p (XR Y)/markedModel g p Y) -
          ∑ j ∈ Finset.range (K+1), logarithmicMarkedCoefficient P p j Y/
            (complexity g p : ℝ)^j| ≤
            C*B^(K+1)*((K+1).factorial : ℝ)^2/(complexity g p : ℝ)^(K+1)) ∧
      (∃ c' a C' h₁ : ℝ, 0 < c' ∧ c' ≤ c ∧ 0 < a ∧ 0 < C' ∧ 0 < h₁ ∧
        ∀ g : ℕ, h₁ ≤ (complexity g p : ℝ) → ∀ Y ∈ Set.Ico 0 y₀,
          |Real.pi*markedF P g p (XR Y)/markedModel g p Y -
            ∑ j ∈ Finset.range (⌊c'*Real.sqrt (complexity g p)⌋₊+1),
              markedCoefficient P p j Y/(complexity g p : ℝ)^j| ≤
                C'*Real.exp (-a*Real.sqrt (complexity g p))) := by
  exact full_expansion_proof P p hp


end WP.HigherOrder
