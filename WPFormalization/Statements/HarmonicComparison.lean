import WPFormalization.Comparison.HarmonicProof

noncomputable section
namespace WP

/- Proposition 5.1, fixed marking count, uniform in all genera/degrees and closed parameter. -/
/- Blueprint label(s): prop:harmonic
Paper v3: 5.1 [PDF 24]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "prop:harmonic"]
theorem harmonic_comparison (P : PsiTheory) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, ∀ d : List ℕ, d.length = n → Stable g n →
    d.sum ≤ dimension g n → ∀ Y ∈ Set.Icc 0 y₀,
      -C*(Real.log (complexity g n+1))^2 ≤ Real.log (ratio P g d Y) ∧
      Real.log (ratio P g d Y) ≤ C*Real.sqrt (complexity g n) := by
  exact harmonic_comparison_proof P n hn

end WP
