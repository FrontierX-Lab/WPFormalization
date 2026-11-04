import WPFormalization.Weighted.Definitions
import WPFormalization.Weighted.LinearBound
import WPFormalization.Weighted.SeparatingBound

/-! The weighted linear and separating sums of §5, with pivot choice and zero conventions. -/
noncomputable section
namespace WP

/- Lemma 5.4. The pivot condition comes from the paragraph immediately preceding the lemma. -/
/- Blueprint label(s): lem:weighted-linear
Paper v3: 5.4 [PDF 27]
Status: CONDITIONALLY_PROVED (registered classical analytic inputs)
-/
@[blueprint "lem:weighted-linear"]
theorem weighted_linear_bound : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c ∈ Set.Ioc 0 c₀,
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ g pivot : ℕ, ∀ d : List ℕ,
      PivotChoice pivot d → ¬ Terminal g (pivot :: d) →
      (pivot :: d).sum ≤ dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
        weightedLinear c Y g pivot d ≤
          1+C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))/complexity g (d.length+1) ∧
        1+C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))/complexity g (d.length+1) ≤
          1+C₂/Real.sqrt (complexity g (d.length+1)) := by
  exact weighted_linear_bound_core

/- Lemma 5.5, η=1/12, all ordered stable separating terms. -/
/- Blueprint label(s): lem:weighted-separating
Paper v3: 5.5 [PDF 27]
Status: CONDITIONALLY_PROVED (registered classical analytic inputs)
-/
@[blueprint "lem:weighted-separating"]
theorem weighted_separating_bound : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c ∈ Set.Ioc 0 c₀,
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ g pivot : ℕ, ∀ d : List ℕ,
      PivotChoice pivot d → ¬ Terminal g (pivot :: d) →
      (pivot :: d).sum ≤ dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
        weightedSeparating c Y g pivot d ≤
          C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))*
            (1+inactive (pivot :: d))/Real.rpow (complexity g (d.length+1)) (3/2 : ℝ) ∧
        C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))*
            (1+inactive (pivot :: d))/Real.rpow (complexity g (d.length+1)) (3/2 : ℝ) ≤
          C₂/Real.sqrt (complexity g (d.length+1)) := by
  exact weighted_separating_bound_core
end WP
