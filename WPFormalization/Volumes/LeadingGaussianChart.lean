import WPFormalization.Statements.Marked
noncomputable section
namespace WP
open Set Complex
set_option autoImplicit false

/-- Local analytic data for the actual leading marked model. The existence
of these data is proved from the origin, compact, and critical constructions;
this predicate contains no estimate for the actual generating function. -/
def LeadingGaussianChart (g p:ℕ)(x R C D:ℝ):Prop:=
  ∃L A:ℂ→ℂ,
    AnalyticOnNhd ℂ L (Metric.ball 0 R) ∧ L 0=0 ∧ coeff L 1=0 ∧ coeff L 2=(1/2:ℂ) ∧
    (∀w:ℂ,‖w‖<R→‖L w‖≤C*‖w‖^2) ∧
    AnalyticOnNhd ℂ A (Metric.ball 0 R) ∧ A 0=1 ∧
    (∀w:ℂ,‖w‖<R→‖A w‖≤D) ∧
    ∀u:ℝ,|u|<R→
      let h:ℝ:=complexity g p
      let σ:ℝ:=Real.sqrt (h*euler Psi x)
      let xt:ℝ:=x*Real.exp (u/σ)
      xt∈Ioo (0:ℝ) xCritical ∧
      Complex.exp (L (u:ℂ))*A (u:ℂ)=
        Complex.exp (-((h*Psi x:ℝ):ℂ)*(u:ℂ)/(σ:ℂ))*
          ((markedModel g p (inverseY xt)/markedModel g p (inverseY x):ℝ):ℂ)

lemma LeadingGaussianChart.mono (g p:ℕ)(x R C D r c d:ℝ)
    (h:LeadingGaussianChart g p x R C D)(hr:r≤R)(hC:C≤c)(hD:D≤d):
    LeadingGaussianChart g p x r c d:=by
  rcases h with ⟨L,A,hLa,hL0,hL1,hL2,hLb,hAa,hA0,hAb,htrace⟩
  refine ⟨L,A,hLa.mono (Metric.ball_subset_ball hr),hL0,hL1,hL2,?_,
    hAa.mono (Metric.ball_subset_ball hr),hA0,?_,?_⟩
  · intro w hw
    exact (hLb w (hw.trans_le hr)).trans (mul_le_mul_of_nonneg_right hC (sq_nonneg ‖w‖))
  · intro w hw
    exact (hAb w (hw.trans_le hr)).trans hD
  · intro u hu
    exact htrace u (hu.trans_le hr)
end WP
