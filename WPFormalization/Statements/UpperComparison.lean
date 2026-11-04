import WPFormalization.Comparison.UpperProof

noncomputable section
namespace WP

/- Lemma 5.6, small positive clipping constant, uniform in the state. -/
/- Blueprint label(s): lem:upper
Paper v3: 5.6 [PDF 29]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:upper"]
theorem comparison_upper (P : PsiTheory) : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ c ∈ Set.Ioc 0 c₀, ∃ C : ℝ, 0 < C ∧
      ∀ g : ℕ, ∀ d : List ℕ, 1 ≤ d.length → Stable g d.length →
      d.sum ≤ dimension g d.length → ∀ Y ∈ Set.Icc 0 y₀,
        ratio P g d Y ≤ C*clippedWeight c d*Real.exp (C*Real.sqrt (complexity g d.length)) := by
  exact comparison_upper_proof P

end WP
