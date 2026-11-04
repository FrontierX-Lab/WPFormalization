import WPFormalization.Comparison.LowerProof

noncomputable section
namespace WP

/- Lemma 5.3, constant independent of the number of markings. -/
/- Blueprint label(s): lem:lower
Paper v3: 5.3 [PDF 25]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:lower"]
theorem comparison_lower (P : PsiTheory) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ g : ℕ, ∀ d : List ℕ, 1 ≤ d.length → Stable g d.length →
    d.sum ≤ dimension g d.length → ∀ Y ∈ Set.Icc 0 y₀,
      c*Real.exp (-C*(zeros d+Real.log (complexity g d.length+1))*
        Real.log (complexity g d.length+1)) ≤ ratio P g d Y := by
  exact comparison_lower_proof P

end WP
