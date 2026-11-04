import WPFormalization.Statements.Coefficients
import WPFormalization.HigherOrder.Triangular
import WPFormalization.HigherOrder.OrderWeights

/-! Frozen actual-remainder substatement of Proposition C.3 (FE7).
This definition asserts no inhabitant. Holomorphy, arbitrary coordinate-path
compatibility, and finite-data dependence are distinct parts of the original
proposition; this substatement is therefore not associated to its Blueprint
label. Every order L>=1 is included, including the large-weight branch. -/
noncomputable section
namespace WP.HigherOrder

def UniformRecursiveRemainderTarget (P : PsiTheory) : Prop :=
  ∃ (C B : ℝ) (M : ℕ), 0<C ∧ 0<B ∧ 2≤M ∧
    (∀ g : ℕ, ∀ d : List ℕ, 1≤d.length → Stable g d.length →
      1≤complexity g d.length → ∀ L : ℕ, 1≤L → ∀ Y∈Set.Icc (0:ℝ) y₀,
      |profile P g d Y-
        ∑ j∈Finset.range L,profileCoefficient P Y d j/(complexity g d.length:ℝ)^j|≤
          C*B^L*profileOrderWeight (M:ℝ) L d^(2*L)/(complexity g d.length:ℝ)^L) ∧
    (∀ g p : ℕ, 1≤p → Stable g p → 1≤complexity g p →
      ∀ L : ℕ, 1≤L → ∀ Y∈Set.Icc (0:ℝ) y₀,
      |cuspCorrection P g p Y-
        ∑ j∈Finset.range L,cuspCoefficient P Y p j/(complexity g p:ℝ)^j|+
      |genusCorrection P g p Y-
        ∑ j∈Finset.range L,genusCoefficient P Y p j/(complexity g p:ℝ)^j|≤
          C*B^L*scalarOrderWeight (M:ℝ) L p^(2*L)/(complexity g p:ℝ)^L)

end WP.HigherOrder
