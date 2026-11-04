import WPFormalization.Statements.AdjacentLimit
import WPFormalization.Coefficients.AdjacentEndpointProof
noncomputable section
namespace WP
open Filter
open scoped Topology

/- Theorem 1.4's small-degree and positive-codimension consequences. -/
/- Blueprint label(s): thm:coefficient
Paper v3: 1.4 [PDF 8]
Status: CONDITIONALLY_PROVED; registered classical inputs remain
-/
@[blueprint "thm:coefficient"]
theorem adjacent_endpoint_limits (P : PsiTheory) :
    (∀ ks : ℕ → ℕ,
      (∀ᶠ g in atTop, ks g < 3*g-2) →
      Tendsto (fun g : ℕ => (ks g : ℝ)/g) atTop (𝓝 0) →
      Tendsto (fun g => boundaryA P g (ks g)/boundaryA P g (ks g+1)) atTop (𝓝 4)) ∧
    (∀ ms : ℕ → ℕ,
      (∀ᶠ g in atTop, 1 ≤ ms g ∧ ms g ≤ 3*g-2) →
      Tendsto (fun g : ℕ => (ms g : ℝ)/g) atTop (𝓝 0) →
      Tendsto (fun g =>
        (boundaryA P g (3*g-2-ms g)/boundaryA P g (3*g-2-ms g+1)) /
          (4*Real.pi^2*g/(5*ms g))) atTop (𝓝 1)) := by
  exact adjacent_endpoint_limits_proof P

end WP
