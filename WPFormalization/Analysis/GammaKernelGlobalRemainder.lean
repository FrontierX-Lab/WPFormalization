import WPFormalization.Analysis.GammaRatioBernoulli
import WPFormalization.Analysis.GlobalTaylorRay
import WPFormalization.Analysis.GammaKernelGrowth
/-! A fixed Cauchy neighborhood and the actual positive-ray tail bound give
one global Taylor remainder valid at every order. No Gamma asymptotic or
classical Laplace identity is used in this analytic kernel estimate. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

lemma gammaRatioKernel_global_taylor_bound (a : ℝ) (ha : 0<a) :
    ∃ C B : ℝ,0<C ∧ 0<B ∧ ∀N:ℕ,∀t:ℝ,0<t →
      ‖gammaRatioKernel a (t:ℂ)-∑i∈Finset.range N,WP.coeff (gammaRatioKernel a) i*(t:ℂ)^i‖≤C*B^N*t^N := by
  obtain ⟨r,hr,hf⟩ := (gammaRatioKernel_analytic_zero a).exists_ball_analyticOnNhd
  let R : ℝ := r/2
  have hR : 0<R := by dsimp only [R];positivity
  have hsub : Metric.closedBall (0:ℂ) R⊆Metric.ball (0:ℂ) r :=
    Metric.closedBall_subset_ball (by dsimp only [R];linarith)
  have hdiff : DifferentiableOn ℂ (gammaRatioKernel a) (Metric.closedBall (0:ℂ) R) :=
    hf.differentiableOn.mono hsub
  obtain ⟨m,hm⟩ := (isCompact_closedBall (0:ℂ) R).bddAbove_image hdiff.continuousOn.norm
  let M : ℝ := max m 1
  have hM : 0≤M := le_trans (by norm_num) (le_max_right m 1)
  have hcircle : ∀z∈Metric.sphere (0:ℂ) R,‖gammaRatioKernel a z‖≤M := by
    intro z hz
    exact (hm ⟨z,Metric.sphere_subset_closedBall hz,rfl⟩).trans (le_max_left m 1)
  obtain ⟨T,hT,htail⟩ := gammaRatioKernel_ray_bounded a (R/2) ha (by positivity)
  refine ⟨T+2*M,2/R,by positivity,by positivity,?_⟩
  intro N t ht
  exact complex_taylor_global_ray_bound (gammaRatioKernel a) R M T hR hM hT.le hdiff hcircle htail N t ht

lemma gammaLogRatioKernel_global_taylor_bound (a : ℝ) (ha : 0<a) :
    ∃ C B : ℝ,0<C ∧ 0<B ∧ ∀N:ℕ,∀t:ℝ,0<t →
      |External.gammaLogRatioKernel a t-∑i∈Finset.range N,WP.realCoeff (gammaRatioKernel a) i*t^i|≤C*B^N*t^N := by
  obtain ⟨C,B,hC,hB,hbound⟩ := gammaRatioKernel_global_taylor_bound a ha
  refine ⟨C,B,hC,hB,?_⟩
  intro N t ht
  have hpoly : (∑i∈Finset.range N,WP.coeff (gammaRatioKernel a) i*(t:ℂ)^i).re=
      ∑i∈Finset.range N,WP.realCoeff (gammaRatioKernel a) i*t^i := by
    change Complex.reCLM (∑i∈Finset.range N,WP.coeff (gammaRatioKernel a) i*(t:ℂ)^i)=_
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Complex.reCLM_apply,Complex.mul_re,←Complex.ofReal_pow,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,WP.realCoeff]
  have hb := (Complex.abs_re_le_norm
    (gammaRatioKernel a (t:ℂ)-∑i∈Finset.range N,WP.coeff (gammaRatioKernel a) i*(t:ℂ)^i)).trans
      (hbound N t ht)
  rw [Complex.sub_re,hpoly,gammaRatioKernel_real a t ha ht,Complex.ofReal_re] at hb
  exact hb

lemma gammaRatioKernel_realCoeff_log (a : ℚ) (n : ℕ) :
    WP.realCoeff (gammaRatioKernel (a:ℝ)) n*(n.factorial:ℝ)=
      PowerSeries.coeff (n+1) (WP.HigherOrder.gammaRatioLog a) := by
  have h := congrArg Complex.re (gammaRatioKernel_coeff_log a n)
  have hr : (n.factorial:ℂ).re=(n.factorial:ℝ) := by simp
  have hi : (n.factorial:ℂ).im=0 := by simp
  simpa only [Complex.mul_re,hr,hi,mul_zero,sub_zero,Complex.ofReal_re,WP.realCoeff] using h

end WP.Analysis
