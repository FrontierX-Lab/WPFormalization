import WPFormalization.Marked.UniformComplexityGrowth
import WPFormalization.Intersection.ProfileMonotone
import WPFormalization.HigherOrder.Triangular

/-! The actual stable nonempty bounded-component amplitudes satisfy a marking- and degree-independent exponential-in-complexity Gamma bound on the closed real interval. This is a real input, not an asserted complex-domain extension of C.21. -/
noncomputable section
namespace WP.HigherOrder
lemma smallW_real_uniform_complexity_bound (P:PsiTheory) :
    ∃T:ℝ,1 ≤ T ∧ ∀g:ℕ,∀d:List ℕ,Stable g d.length→1 ≤ d.length→
      ∀Y∈Set.Icc (0:ℝ) y₀,
      |smallW P Y g d| ≤ Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length) := by
  obtain ⟨T,hT,hbound⟩:=W_uniform_complexity_exponential P
  refine ⟨T,hT,?_⟩
  intro g d hs hd Y hY
  have hn : 0 ≤ smallW P Y g d := mul_nonneg (by positivity) (normalized_nonneg_nonempty P g d hd Y hY)
  rw [abs_of_nonneg hn]
  have he:=mul_le_mul_of_nonneg_left (normalized_le_all_zero P g d hs Y hY)
    (show (0:ℝ) ≤ (4:ℝ)^g by positivity)
  exact he.trans (hbound g d.length hs Y hY)
end WP.HigherOrder
