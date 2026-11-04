import WPFormalization.Statements.Basic
import WPFormalization.Statements.PoissonDefinitions
import WPFormalization.Statements.PhaseChangeDefinitions
import WPFormalization.HigherOrder.PoissonPhaseChangeProof
import WPFormalization.HigherOrder.PoissonCentralOriginalProof

/-! Appendix D's analytic phase and signed Poisson central coefficient calculus.
Coefficients are defined by the stated exponential generating function, not by
arbitrary functions satisfying the desired estimates. -/
noncomputable section
namespace WP

/- Lemma D.6. The same C bounds all orders up to h/2 and all central indices. -/
/- Blueprint label(s): lem:poisson-central
Paper v3: D.6 [PDF 93]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:poisson-central"]
theorem poisson_central_expansion (R : ℝ) (hR : 0 < R) (f : ℂ × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R ×ˢ Metric.ball 0 R))
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) R ×ˢ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ 1) :
    ∃ ν₀ ρ C : ℝ, 0 < ν₀ ∧ 0 < ρ ∧ 0 < C ∧
      (∀ h k K : ℕ, 1 ≤ h → (k : ℝ)/h ≤ ν₀ → 2*K ≤ h →
        ‖poissonOperator f h k -
          ∑ j ∈ Finset.range (K+1), (h : ℂ)⁻¹^j * poissonCorrection f j ((k : ℂ)/h)‖ ≤
          C^(K+1)*(K+1).factorial/(h : ℝ)^(K+1)) ∧
      (∀ j : ℕ, AnalyticOnNhd ℂ (poissonCorrection f j) (Metric.ball 0 ρ) ∧
        ∀ ν : ℂ, ‖ν‖ < ρ → ‖poissonCorrection f j ν‖ ≤ C^(j+1)*j.factorial) ∧
      (∀ j : ℕ, 1 ≤ j → poissonCorrection f j 0 = 0) ∧
      (∀ h k : ℕ, 1 ≤ h → (k : ℝ)/h ≤ ν₀ → ‖poissonOperator f h k‖ ≤ C) := by
  exact poisson_central_expansion_original_proof R hR f hf hbound

/- Lemma D.5. Uses log(Z/u) and the removable ν/x quotient to specify the
local analytic logarithms even at u=0 or ν=0; includes the coefficient identity. -/
/- Blueprint label(s): lem:phase-change
Paper v3: D.5 [PDF 92]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:phase-change"]
theorem analytic_phase_change (S : ℂ → ℂ) (hS : AnalyticAt ℂ S 0) (hzero : S 0 = 0)
    (hsreal : (deriv S 0).im = 0) (hspos : 0 < (deriv S 0).re) :
    ∃ R : ℝ, 0 < R ∧ ∃ x Q : ℂ → ℂ, ∃ Z : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ x (Metric.ball 0 R) ∧
      AnalyticOnNhd ℂ Q (Metric.ball 0 R) ∧
      AnalyticOnNhd ℂ Z (Metric.ball 0 R ×ˢ Metric.ball 0 R) ∧
      x 0 = 0 ∧ deriv x 0 = (deriv S 0)⁻¹ ∧ Q 0 = deriv S 0 ∧
      (∀ ν : ℂ, ‖ν‖ < R → x ν*deriv S (x ν) = ν ∧
        (ν ≠ 0 → Q ν = ν/x ν) ∧ Z (0,ν) = 0 ∧ Z (ν,ν) = x ν) ∧
      (∀ u ν : ℂ, ‖u‖ < R → ‖ν‖ < R →
        phaseQuotient Z u ν ≠ 0 ∧
        S (Z (u,ν))-u-ν*Complex.log (phaseQuotient Z u ν) =
          S (x ν)-ν+ν*Complex.log (Q ν)) ∧
      (∀ H : ℂ → ℂ, AnalyticAt ℂ H 0 → ∃ δ : ℝ, 0 < δ ∧
        AnalyticOnNhd ℂ (phaseAmplitude Z H) (Metric.ball 0 δ ×ˢ Metric.ball 0 δ) ∧
        ∀ h k : ℕ, 1 ≤ h → (k : ℝ)/h < δ →
          let ν : ℂ := (k : ℂ)/h
          coeff (fun z => Complex.exp (h*S z)*H z) k =
            Complex.exp (h*(S (x ν)-ν+ν*Complex.log (Q ν))) *
              coeff (fun u => Complex.exp (h*u)*phaseAmplitude Z H (u,ν)) k) := by
  exact analytic_phase_change_proof S hS hzero hsreal hspos
end WP
