import WPFormalization.Analysis.BorelSlitContour
import WPFormalization.Analysis.WeightedRayTail
import Mathlib

/-! Weighted L1 control on each fixed off-cut ray gives a proved norm bound
for the unchanged infinite tail, including its fixed exponential gap. -/
noncomputable section
namespace WP.Analysis
open Complex MeasureTheory Set Filter Metric

def laplaceRayIntegrand (H : ℂ → ℂ) (θ ξ t : ℝ) : ℂ :=
  Complex.exp ((θ:ℂ)*Complex.I)*
    laplaceSlitFunction H ξ ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))

def laplaceRayTail (H : ℂ → ℂ) (θ ξ A : ℝ) : ℂ :=
  ∫ t in Ioi A,laplaceRayIntegrand H θ ξ t

lemma norm_laplaceRayIntegrand (H : ℂ → ℂ) (θ ξ t : ℝ) :
    ‖laplaceRayIntegrand H θ ξ t‖=Real.exp (-((ξ*Real.cos θ)*t))*
      ‖H ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖ := by
  unfold laplaceRayIntegrand laplaceSlitFunction
  have hu : ‖Complex.exp ((θ:ℂ)*Complex.I)‖=1 := by rw [Complex.norm_exp];simp
  rw [norm_mul,hu,one_mul,norm_mul,Complex.norm_exp]
  have he : (-(ξ:ℂ)*((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))).re=-((ξ*Real.cos θ)*t) := by
    simp [Complex.exp_re]
    ring
  rw [he]

lemma laplaceRayTail_of_weighted_L1 (H : ℂ → ℂ) (θ ξ A b U : ℝ)
    (hH : AnalyticOnNhd ℂ H firstBorelSlit) (hsin : Real.sin θ≠0)
    (hA : 0≤A) (hξ : b≤ξ*Real.cos θ)
    (hi : IntegrableOn (fun t:ℝ => Real.exp (-(b*t))*
      ‖H ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖) (Ioi 0))
    (hU : (∫ t in Ioi 0,Real.exp (-(b*t))*
      ‖H ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖)≤U) :
    IntegrableOn (laplaceRayIntegrand H θ ξ) (Ioi A) ∧
      ‖laplaceRayTail H θ ξ A‖≤Real.exp (-((ξ*Real.cos θ-b)*A))*U := by
  have hf := analyticOnNhd_laplaceSlitFunction H hH ξ
  have hc : ContinuousOn (laplaceRayIntegrand H θ ξ) (Ioi A) := by
    apply ContinuousOn.mul continuous_const.continuousOn
    apply hf.continuousOn.comp (by fun_prop)
    intro t ht
    exact slit_radial_mem t θ (hA.trans ht.le) hsin
  apply weighted_ray_tail_norm_bound (laplaceRayIntegrand H θ ξ)
    (fun t:ℝ => ‖H ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖) A b (ξ*Real.cos θ) U hA hξ
    (fun t _ => norm_nonneg _) hi hU (hc.aestronglyMeasurable measurableSet_Ioi)
  intro t ht
  exact (norm_laplaceRayIntegrand H θ ξ t).le

lemma laplaceRayTail_exponential_gap (H : ℂ → ℂ) (θ ξ A b U : ℝ)
    (hH : AnalyticOnNhd ℂ H firstBorelSlit) (hsin : Real.sin θ≠0)
    (hA : 0<A) (hb : 0≤b) (hU0 : 0≤U)
    (hgap : 0<A*Real.cos θ-1) (hξ0 : 0≤ξ)
    (hξ : 2*b*A/(A*Real.cos θ-1)≤ξ)
    (hi : IntegrableOn (fun t:ℝ => Real.exp (-(b*t))*
      ‖H ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖) (Ioi 0))
    (hU : (∫ t in Ioi 0,Real.exp (-(b*t))*
      ‖H ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖)≤U) :
    ‖laplaceRayTail H θ ξ A‖≤U*Real.exp (-((1+(A*Real.cos θ-1)/2)*ξ)) := by
  have hκ : 2*b*A≤ξ*(A*Real.cos θ-1) := (div_le_iff₀ hgap).mp hξ
  have hcos : 0<Real.cos θ := by nlinarith
  have hq : b≤ξ*Real.cos θ := by nlinarith [mul_nonneg hb hA.le]
  have hnorm := (laplaceRayTail_of_weighted_L1 H θ ξ A b U hH hsin hA.le hq hi hU).2
  apply hnorm.trans
  rw [mul_comm U]
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr _) hU0
  nlinarith
end WP.Analysis
