import WPFormalization.Weighted.SeparatingMass
import WPFormalization.Weighted.SeparatingScale

/-! The complete original quantified separating bound, with its exact original hypotheses and constants. -/
noncomputable section
namespace WP
theorem weighted_separating_bound_core : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c ∈ Set.Ioc 0 c₀,
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ g pivot : ℕ, ∀ d : List ℕ,
      PivotChoice pivot d → ¬ Terminal g (pivot :: d) →
      (pivot :: d).sum ≤ dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
        weightedSeparating c Y g pivot d ≤
          C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))*
            (1+inactive (pivot :: d))/Real.rpow (complexity g (d.length+1)) (3/2 : ℝ) ∧
        C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))*
            (1+inactive (pivot :: d))/Real.rpow (complexity g (d.length+1)) (3/2 : ℝ) ≤
          C₂/Real.sqrt (complexity g (d.length+1)) := by
  refine ⟨1,by norm_num,?_⟩
  intro c hc
  obtain ⟨C₁,hC₁,hbound⟩ := weightedSeparating_mass_bound c hc.1
  obtain ⟨C₂,hC₂,hscale⟩ := weightedSeparating_sqrt_envelope C₁ hC₁
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  intro g pivot d hchoice hNt hd Y hY
  have hg : 2≤g := by
    unfold Terminal at hNt
    push_neg at hNt
    omega
  exact ⟨hbound g pivot d hg hd Y hY,hscale g pivot d hg hd Y hY⟩
end WP
