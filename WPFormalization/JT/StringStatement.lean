import WPFormalization.JT.StringNormalization

/-! Section 15.1: the complete cusp-defect string and volume normalization
statement, separated from the series and geometric-bridge implementation. -/
noncomputable section
universe u v
namespace WP.JT
open Set WP.External

/- The string equation is the exact X equation, its undeformed-connected
inverse branch includes the critical endpoint, and the true geometric genus
amplitude has the exact factor (2π²)^(3g−3) on its convergence domain. -/
@[blueprint "eq:jt-string-normalization"]
theorem string_normalization (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P) :
    (∀ Y lambdaDef : ℝ,
      stringBesselEnergy (edgeEnergy Y)+lambdaDef=0 ↔ XR Y=2*Real.pi^2*lambdaDef) ∧
    (∀ lambdaDef : ℝ, 0 ≤ lambdaDef → 2*Real.pi^2*lambdaDef ≤ xCritical →
      inverseY (2*Real.pi^2*lambdaDef) ∈ Icc 0 y₀ ∧
      stringBesselEnergy (edgeEnergy (inverseY (2*Real.pi^2*lambdaDef)))+lambdaDef=0 ∧
      ∀ Y ∈ Icc 0 y₀, stringBesselEnergy (edgeEnergy Y)+lambdaDef=0 →
        Y=inverseY (2*Real.pi^2*lambdaDef)) ∧
    edgeEnergy (inverseY 0)=0 ∧
    (∀ g : ℕ, 2 ≤ g → ∀ lambdaDef : ℝ, |2*Real.pi^2*lambdaDef| < xCritical →
      HasSum (fun n : ℕ => cuspVolume G g n*lambdaDef^n/(n.factorial : ℝ))
        ((2*Real.pi^2)^(3*g-3)*(Phi P g (2*Real.pi^2*lambdaDef)).re)) := by
  exact ⟨string_equation_iff, string_equation_branch_closed,
    edgeEnergy_inverse_zero, geometric_defect_amplitude P G⟩

end WP.JT
