import WPFormalization.Analysis.KernelMomentBounds
import WPFormalization.Analysis.WeightNonnegative
noncomputable section
namespace WP
/- Full original Eq.2.7. The actual deflated first-root quotient has a common
analytic nonvanishing disk, so Cauchy yields geometric coefficient decay
and all uniform absolute moments. Its actual positive higher-root product
proves coefficient nonnegativity; finite telescoping proves theta bounds.
Blueprint label(s): eq:P11
Paper v3: 2.7 [PDF17]
Status: CONDITIONALLY_PROVED (precisely registered classical kernel inputs)
-/
@[blueprint "eq:P11"]
theorem uniform_kernel_moments :
    (∃ C : ℝ, ∀ Y ∈ Set.Icc 0 y₀,
      theta Y 0 = 1 ∧ Monotone (theta Y) ∧ ∀ l, theta Y l ≤ C ∧ 0 ≤ weight Y l) ∧
    (∀ q : ℕ, ∃ C : ℝ, ∀ Y ∈ Set.Icc 0 y₀,
      Summable (fun l : ℕ => (1+(l : ℝ))^q * weight Y l) ∧
      ∑' l : ℕ, (1+(l : ℝ))^q * weight Y l ≤ C)  := by
  obtain ⟨C,hC⟩:=Analysis.theta_uniform_bound
  refine ⟨⟨C,?_⟩,Analysis.weight_moments_uniform⟩
  intro Y hY
  refine ⟨Analysis.theta_zero_closed Y hY,
    Analysis.theta_monotone_of_weight_nonneg Y (fun n=>weight_nonneg Y hY n),?_⟩
  intro n
  exact ⟨hC Y hY n,weight_nonneg Y hY n⟩

end WP
