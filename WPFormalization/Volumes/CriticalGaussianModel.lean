import WPFormalization.Volumes.CriticalGaussianAmplitudes
import WPFormalization.Analysis.GaussianModelRemainder
import WPFormalization.Analysis.ParameterTaylorAnalytic
/-! The actual marked amplitude family yields auxiliary transformed Gaussian
coefficients on a common critical parameter disk, with uniform Gevrey-two
bounds and leading coefficient one. The original CG3 identification remains
separate; this module does not replace any prescribed extraction coefficient. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace WP.Analysis
lemma gaussian_model_coefficient_parameter_analyticAt (F:ℕ → ℂ × ℂ → ℂ) (p:ℂ) (j:ℕ)
    (hF:∀s,AnalyticAt ℂ (F s) (p,0)) :
    AnalyticAt ℂ (fun q:ℂ=>gaussianModelCoefficient (fun s u=>F s (q,u)) j) p := by
  apply Finset.analyticAt_fun_sum
  intro s hs
  exact (parameter_taylor_coefficient_analyticAt (F s) p (2*(j-s)) (hF s)).mul analyticAt_const
lemma CriticalGaussianCoordinateData.actual_gaussian_model_coefficient_family
    (d:CriticalGaussianCoordinateData) (P:PsiTheory) (p:ℕ) (hp:1 ≤ p) :
    ∃ (Q:ℂ → ℂ) (Ω:Set ℂ) (f:ℕ → ℂ → ℂ) (ρ C B:ℝ),
      AnalyticAt ℂ Q 0 ∧ Q 0=1 ∧
      (∀ᶠδ:ℝ in 𝓝 0,0<δ → Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)) ∧
      IsOpen Ω ∧ (∀Y ∈ Set.Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω) ∧
      (∀j,AnalyticOnNhd ℂ (f j) Ω) ∧
      (∀j Y,Y ∈ Set.Icc (0:ℝ) y₀ → f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ)) ∧
      0<ρ ∧ 0<C ∧ 0<B ∧
      (∀δ:ℂ,‖δ‖<ρ → ∀s,DifferentiableOn ℂ
        (fun u:ℂ=>d.modelAmplitude Q p f s (δ,u)) (Metric.closedBall 0 ρ)) ∧
      (∀(s:ℕ) (δ u:ℂ),‖δ‖<ρ → ‖u‖ ≤ ρ →
        ‖d.modelAmplitude Q p f s (δ,u)‖ ≤ C*B^s*(s.factorial:ℝ)^2) ∧
      (∀j,AnalyticOnNhd ℂ (fun δ:ℂ=>gaussianModelCoefficient
        (fun s u=>d.modelAmplitude Q p f s (δ,u)) j) (Metric.ball 0 ρ)) ∧
      (∀(j:ℕ) (δ:ℂ),‖δ‖<ρ → ‖gaussianModelCoefficient
        (fun s u=>d.modelAmplitude Q p f s (δ,u)) j‖ ≤ C*(2*max B (2/ρ^2))^j*(j.factorial:ℝ)^2) ∧
      ∀δ:ℂ,‖δ‖<ρ → gaussianModelCoefficient (fun s u=>d.modelAmplitude Q p f s (δ,u)) 0=1 := by
  obtain ⟨Q,Ω,f,ρ₀,C,B,hQ,hQ0,hQphys,hΩ,hcover,hf,hrest,hρ₀,hC,hB,hmodel,hbound,hzero⟩:=
    d.actual_model_amplitudes P p hp
  let ρ:ℝ:=ρ₀/2
  have hρ:0<ρ:=half_pos hρ₀
  have hρlt:ρ<ρ₀:=by dsimp[ρ];linarith
  have hpoint (δ u:ℂ)(hδ:‖δ‖<ρ)(hu:‖u‖ ≤ ρ):
      ((δ,u):ℂ × ℂ) ∈ Metric.ball 0 ρ₀ := by
    rw [Metric.mem_ball,dist_zero_right,Prod.norm_def,max_lt_iff]
    exact ⟨hδ.trans hρlt,hu.trans_lt hρlt⟩
  have hDiff (δ:ℂ)(hδ:‖δ‖<ρ)(s:ℕ):DifferentiableOn ℂ
      (fun u:ℂ=>d.modelAmplitude Q p f s (δ,u)) (Metric.closedBall 0 ρ) := by
    intro u hu
    rw [Metric.mem_closedBall,dist_zero_right] at hu
    exact (hmodel s (δ,u) (hpoint δ u hδ hu)).curry_right.differentiableAt.differentiableWithinAt
  have hBd(s:ℕ)(δ u:ℂ)(hδ:‖δ‖<ρ)(hu:‖u‖ ≤ ρ):
      ‖d.modelAmplitude Q p f s (δ,u)‖ ≤ C*B^s*(s.factorial:ℝ)^2 :=
    hbound s δ u (hδ.trans hρlt) (hu.trans_lt hρlt)
  refine ⟨Q,Ω,f,ρ,C,B,hQ,hQ0,hQphys,hΩ,hcover,hf,hrest,hρ,hC,hB,hDiff,hBd,?_,?_,?_⟩
  · intro j δ hδ
    have hd:‖δ‖<ρ:=by simpa only [Metric.mem_ball,dist_zero_right] using hδ
    exact gaussian_model_coefficient_parameter_analyticAt (fun s=>d.modelAmplitude Q p f s) δ j
      (fun s=>hmodel s (δ,0) (hpoint δ 0 hd (by simpa using hρ.le)))
  · intro j δ hδ
    exact gaussian_model_coefficients_gevrey_two _ C B ρ hC.le hB.le hρ (hDiff δ hδ)
      (fun s u hu=>hBd s δ u hδ (by simpa only [Metric.mem_sphere,dist_zero_right] using le_of_eq hu)) j
  · intro δ hδ
    simpa [gaussianModelCoefficient,WP.coeff] using hzero δ (hδ.trans hρlt)
end WP.Analysis
