import WPFormalization.Statements.CoefficientBoundsTarget
import WPFormalization.Statements.RecursiveRemainderTarget
import WPFormalization.Statements.FiniteKernelDataTarget
import WPFormalization.HigherOrder.TriangularLocality

/-! Full Proposition C.3 specification, fixed before its final assembly.
One common C/B/M and one common complex domain govern the genuine canonical
coefficients and every finite-genus remainder. The exact complex adjacent rule
expresses path compatibility; the separate finite-data and boundary-polynomial
conclusions retain the final paragraph of the original proof. No producer is
asserted in this specification, and it is not yet associated to the Blueprint. -/
noncomputable section
namespace WP.HigherOrder
open Set

def UniformRecursiveExpansionsTarget (P : PsiTheory) : Prop :=
  ∃ (Ω : Set ℂ) (R : ℂ → ℂ) (C B : ℝ) (M : ℕ),
    IsOpen Ω ∧ Convex ℝ Ω ∧
    (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧ 0<C ∧ 0<B ∧ 2≤M ∧
    AnalyticOnNhd ℂ R Ω ∧
    (∀ z∈Ω,WP.Analysis.complexAUnit z≠0) ∧
    (∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 ∧
    (∀ Y∈Icc (0:ℝ) y₀,∀ w : ℂ,
      WP.Analysis.regularizedKernel K R (Y:ℂ) w=barK Y w ∧
      WP.Analysis.regularizedKernel H R (Y:ℂ) w=barH Y w) ∧
    (∀ j : ℕ,∀ d : List ℕ,1≤d.length →
      AnalyticOnNhd ℂ (fun z=>ComplexCanonical.profileCoefficient P R z d j) Ω) ∧
    (∀ j p : ℕ,1≤p → AnalyticOnNhd ℂ (fun z=>ComplexCanonical.cuspCoefficient P R z p j) Ω ∧
      AnalyticOnNhd ℂ (fun z=>ComplexCanonical.genusCoefficient P R z p j) Ω) ∧
    (∀ j : ℕ,∀ d : List ℕ,1≤d.length → ∀ Y∈Icc (0:ℝ) y₀,
      ComplexCanonical.profileCoefficient P R (Y:ℂ) d j=(WP.HigherOrder.profileCoefficient P Y d j:ℂ)) ∧
    (∀ j p : ℕ,1≤p → ∀ Y∈Icc (0:ℝ) y₀,
      ComplexCanonical.cuspCoefficient P R (Y:ℂ) p j=(WP.HigherOrder.cuspCoefficient P Y p j:ℂ) ∧
      ComplexCanonical.genusCoefficient P R (Y:ℂ) p j=(WP.HigherOrder.genusCoefficient P Y p j:ℂ)) ∧
    (∀ j : ℕ,∀ d : List ℕ,1≤d.length → ∀ z∈Ω,
      ‖ComplexCanonical.profileCoefficient P R z d j‖≤C*B^j*profileOrderWeight (M:ℝ) j d^(2*j)) ∧
    (∀ j p : ℕ,1≤p → ∀ z∈Ω,
      ‖ComplexCanonical.cuspCoefficient P R z p j‖+‖ComplexCanonical.genusCoefficient P R z p j‖≤
        C*B^j*scalarOrderWeight (M:ℝ) j p^(2*j)) ∧
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
          C*B^L*scalarOrderWeight (M:ℝ) L p^(2*L)/(complexity g p:ℝ)^L) ∧
    (∀ K : ℕ, 0 < K → ∀ d : List ℕ, 1 ≤ d.length → ∀ i : ℕ, i < d.length →
      ∀ z∈Ω,
        ComplexCanonical.profileCoefficient P R z (raiseDegree d i) K-
          ComplexCanonical.profileCoefficient P R z d K=
          ComplexCanonical.adjacentCoefficient P R z
            (ComplexCanonical.hierarchyJet P R z (K-1)) K i d) ∧
    KernelFiniteData.PolynomialDependenceTarget P ∧
    KernelFiniteData.ProfileBoundaryPolynomialTarget P

end WP.HigherOrder
