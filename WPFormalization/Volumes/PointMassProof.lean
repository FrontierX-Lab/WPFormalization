import WPFormalization.Volumes.PointMassAssembly
import WPFormalization.Volumes.CriticalArcFourier

/-! The original Lemma 9.3 follows from its actual local critical arc,
its closed-disk outer bound, and the positive-series Fourier estimate. -/
noncomputable section
namespace WP
theorem point_mass_bound_proof (P : PsiTheory) (c₀ : ℝ) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ h h' : ℕ, 1 ≤ h → 16 ≤ h' → c₀*h ≤ h' →
    ∀ x ∈ Set.Ioo 0 xCritical, ∀ R : ℂ → ℂ,
      AnalyticOnNhd ℂ R (Metric.ball 0 xCritical) →
      (∀ j, 0 ≤ realCoeff R j ∧ (coeff R j).im = 0) → 0 < (R x).re → (R x).im = 0 →
      (∀ z : ℂ, ‖z‖ < xCritical → HasSum (fun j => coeff R j*z^j) (R z)) →
      ∀ j : ℕ,
        realCoeff (fun z => universalV P z^h'*R z) j*x^j /
          (universalV P x^h'*R x).re ≤ C/Real.sqrt (h*euler Psi x) := by
  apply PositiveConvolution.point_mass_bound_of_arc P ?_ c₀ hc
  obtain ⟨δ, ε0, hδ, hε0, hArc⟩ := Analysis.universalV_critical_small_arc_bound P
  refine ⟨δ, ε0, hδ, hε0, ?_⟩
  intro ε hε θ hθ hnear
  simpa only [Analysis.criticalRayPoint, Real.rpow_eq_pow] using hArc ε hε θ hnear
end WP
