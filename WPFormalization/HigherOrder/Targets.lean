import WPFormalization.HigherOrder.CanonicalExpansionStatement
import WPFormalization.HigherOrder.CanonicalExtractionStatement
import WPFormalization.HigherOrder.IntroAbsoluteProof
/-! Original Theorem 1.1. Its full geometric statement is preserved; all
realization inputs remain explicit, and no geometric instance is inferred. -/
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology

/- Theorem 1.1, for an explicit geometric realization and its actual total measure.
No realization or existence is inferred from PsiTheory alone. -/
@[blueprint "thm:intro-absolute"]
theorem intro_absolute (P : PsiTheory) (G : External.WeilPeterssonGeometry P) :
    ∃ C B c : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ ∃ g₀ : ℕ, 0 < g₀ ∧
      (∀ (g : ℕ), g₀ ≤ g → ∀ (K : ℕ),
        (K : ℝ) ≤ c*Real.sqrt (2*(g : ℝ)-1) → ∀ n : ℕ,
        |External.cuspVolume G g n/leadingVolume g n -
          ∑ j ∈ Finset.range (K+1), absoluteCoefficient P j g n/(2*(g : ℝ)-1)^j| ≤
          C*B^(K+1)*((K+1).factorial : ℝ)^2/(2*(g : ℝ)-1)^(K+1)) ∧
      (∀ (g : ℕ), g₀ ≤ g → ∀ j n : ℕ,
        |absoluteCoefficient P j g n| ≤ C*B^j*(j.factorial : ℝ)^2) ∧
      (∃ C' : ℝ, 0 < C' ∧ ∀ (g : ℕ), g₀ ≤ g → ∀ n : ℕ,
        |External.cuspVolume G g n/leadingVolume g n-1| ≤ C'/(g : ℝ)) ∧
      (∃ c' a C' : ℝ, 0 < c' ∧ c' ≤ c ∧ 0 < a ∧ 0 < C' ∧
        ∀ (g : ℕ), g₀ ≤ g → ∀ n : ℕ,
          |External.cuspVolume G g n/leadingVolume g n -
            ∑ j ∈ Finset.range (⌊c'*Real.sqrt (2*(g : ℝ)-1)⌋₊+1),
              absoluteCoefficient P j g n/(2*(g : ℝ)-1)^j| ≤
                C'*Real.exp (-a*Real.sqrt (2*(g : ℝ)-1))) := by
  exact intro_absolute_proof P G

end WP.HigherOrder
