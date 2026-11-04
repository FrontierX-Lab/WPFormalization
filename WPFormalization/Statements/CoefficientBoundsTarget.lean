import WPFormalization.HigherOrder.ComplexCanonicalInputs
import WPFormalization.HigherOrder.OrderWeights
noncomputable section
open Set
namespace WP.HigherOrder.ComplexCanonical
/- Original Lemma C.4 specification, frozen before the proof. No inhabitant or existence is asserted by this definition. The fixed canonical coefficients are the actual triangular algorithm; arbitrary-path compatibility and finite-genus remainders remain separate Proposition C.3 obligations. -/
def CanonicalCoefficientBoundsTarget (P : PsiTheory) : Prop :=
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
      AnalyticOnNhd ℂ (fun z=>profileCoefficient P R z d j) Ω) ∧
    (∀ j p : ℕ,1≤p → AnalyticOnNhd ℂ (fun z=>cuspCoefficient P R z p j) Ω ∧
      AnalyticOnNhd ℂ (fun z=>genusCoefficient P R z p j) Ω) ∧
    (∀ j : ℕ,∀ d : List ℕ,1≤d.length → ∀ Y∈Icc (0:ℝ) y₀,
      profileCoefficient P R (Y:ℂ) d j=(WP.HigherOrder.profileCoefficient P Y d j:ℂ)) ∧
    (∀ j p : ℕ,1≤p → ∀ Y∈Icc (0:ℝ) y₀,
      cuspCoefficient P R (Y:ℂ) p j=(WP.HigherOrder.cuspCoefficient P Y p j:ℂ) ∧
      genusCoefficient P R (Y:ℂ) p j=(WP.HigherOrder.genusCoefficient P Y p j:ℂ)) ∧
    (∀ j : ℕ,∀ d : List ℕ,1≤d.length → ∀ z∈Ω,
      ‖profileCoefficient P R z d j‖≤C*B^j*profileOrderWeight (M:ℝ) j d^(2*j)) ∧
    (∀ j p : ℕ,1≤p → ∀ z∈Ω,
      ‖cuspCoefficient P R z p j‖+‖genusCoefficient P R z p j‖≤
        C*B^j*scalarOrderWeight (M:ℝ) j p^(2*j))
end WP.HigherOrder.ComplexCanonical
