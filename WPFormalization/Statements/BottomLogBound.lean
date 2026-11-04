import WPFormalization.Coefficients.BottomLogBoundProof
noncomputable section
namespace WP
open Filter
open scoped Topology

/- Blueprint label(s): eq:C23
Paper v3: 13.23 [PDF 55]
Status: CONDITIONALLY_PROVED; registered classical inputs remain
-/
@[blueprint "eq:C23"]
theorem bottom_log_bound (P : PsiTheory) : ∃ C : ℝ, 0 < C ∧
    ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ, k ≤ 3*g-2 →
      0 ≤ Real.log (volumeModel P g 1/bracketB P g k) ∧
      Real.log (volumeModel P g 1/bracketB P g k) ≤
        C*(Real.log (g+1))^2+C*(k+1 : ℝ)^2/g := by
  exact bottom_log_bound_proof P

end WP
