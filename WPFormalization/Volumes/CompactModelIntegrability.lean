import WPFormalization.Volumes.CompactGivenModelData
/-! Uniform central-axis integrability of the literal given finite compact model follows from the same common analytic tube, the native J budget and the true base-factor lower bound. This is a proved local analytic helper; the actual comparison client supplies its data. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory
lemma compact_finite_model_axis_integrable_at (P : PsiTheory) (Bc S l : ℂ → ℂ)
    (f : ℕ → ℂ → ℂ) (x : ℂ) (r C B h T : ℝ) (J : ℕ)
    (hr : 0 < r) (hC : 0 ≤ C) (hB : 0 < B) (hh : 0 < h)
    (hTR : T < r * Real.sqrt h)
    (hphase : ∀ u : ℂ, ‖u‖ < r → AnalyticAt ℂ (centeredExponentialPhase S l) (x,u) ∧
      ‖centeredExponentialPhase S l (x,u)‖ ≤ ‖u‖^2)
    (hamp : ∀ j u, ‖u‖ < r → AnalyticAt ℂ (compactPremorseAmplitude P Bc l f j) (x,u) ∧
      ‖compactPremorseAmplitude P Bc l f j (x,u)‖ ≤ C * B^j * (j.factorial : ℝ)^2)
    (hbudget : 2 * B * ((J : ℝ) + 1)^2 ≤ h)
    (hbase : 1/2 ≤ ‖HigherOrder.finiteMarkedFactor f h J (PositiveConvolution.planarInverse P x)‖) :
    IntegrableOn (fun t : ℝ => compactCenteredFiniteModel P Bc S l f h J x (Complex.I*(t : ℂ)))
      (Icc (-T) T) := by
  have hmodel := compact_centered_finite_model_growth_at P Bc S l f x r C B h J
    hr hC hB hh hphase hamp hbudget hbase
  apply ContinuousOn.integrableOn_Icc
  intro t ht
  have hz : Complex.I*(t : ℂ) ∈ Metric.ball (0 : ℂ) (r * Real.sqrt h) := by
    rw [Metric.mem_ball,dist_zero_right,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (abs_le.mpr ht).trans_lt hTR
  have hct : ContinuousAt
      (fun s : ℝ => compactCenteredFiniteModel P Bc S l f h J x (Complex.I*(s : ℂ))) t := by
    exact ContinuousAt.comp
      (g := compactCenteredFiniteModel P Bc S l f h J x)
      (f := fun s : ℝ => Complex.I*(s : ℂ))
      (hmodel.1 _ hz).continuousAt (by fun_prop)
  exact hct.continuousWithinAt
end WP.Analysis
