import WPFormalization.Coefficients.UniformSaddleProof
/- Lemma E.2; the total Real.log convention includes the zero coefficient endpoint. -/
noncomputable section
namespace WP

/- Blueprint label(s): lem:uniform-saddle
Paper v3: E.2 [PDF 98]
Status: CONDITIONALLY_PROVED; registered classical kernel inputs remain
-/
@[blueprint "lem:uniform-saddle"]
theorem uniform_saddle : ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 1 ≤ h → ∀ m : ℕ,
    2*m ≤ 3*h →
    |Real.log (unscaledCoeff h m) + (h : ℝ)*Real.log (H 0 (saddleZeta ((m : ℝ)/h))).re +
      (m : ℝ)*Real.log (saddleZeta ((m : ℝ)/h))| ≤ C*Real.log (h+1) := by
  exact uniform_saddle_proof

end WP
