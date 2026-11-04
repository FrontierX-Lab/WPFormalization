import WPFormalization.Statements.KernelCalculus

/-! Parameter differentiation and a first-moment identity for the actual kernel
integral. These are consequences of differentiation under the integral and FTC. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Metric
open scoped Topology

lemma hasDerivAt_affineIntegral (q A B : ℝ → ℂ)
    (hq : Continuous q) (hA : Continuous A) (hB : Continuous B)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (z : ℂ) :
    HasDerivAt (fun w : ℂ => ∫ s : ℝ in (0)..1, q s * g (A s + w * B s))
      (∫ s : ℝ in (0)..1, q s * B s * deriv g (A s + z * B s)) z := by
  let F (w : ℂ) (s : ℝ) := q s * g (A s + w * B s)
  let F' (w : ℂ) (s : ℝ) := q s * B s * deriv g (A s + w * B s)
  have hc : Continuous g := hg.continuous
  have hc' : Continuous (deriv g) := continuous_iff_continuousAt.mpr
    (fun w => ((hg.analyticAt w).deriv).continuousAt)
  have hF (w : ℂ) : Continuous (F w) := by dsimp [F]; fun_prop
  have hF' : Continuous (fun p : ℂ × ℝ => F' p.1 p.2) := by dsimp [F']; fun_prop
  obtain ⟨C,hC⟩ := ((isCompact_closedBall z 1).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).bddAbove_image hF'.norm.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => C) (ball_mem_nhds z zero_lt_one)
    ?_ ((hF z).intervalIntegrable 0 1) ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards with w
    exact (hF w).aestronglyMeasurable
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards with s hs w hw
    apply hC
    exact ⟨(w,s), ⟨mem_closedBall.mpr (le_of_lt (mem_ball.mp hw)),
      by simpa using Ioc_subset_Icc_self hs⟩, rfl⟩
  · filter_upwards with s hs w hw
    dsimp [F,F']
    convert ((hg _).hasDerivAt.comp w
      (((hasDerivAt_id w).mul_const (B s)).const_add (A s))).const_mul (q s)
      using 1 <;> dsimp only [Function.comp_def, id_eq] <;> ring

lemma kernelIntegral_first_moment (g : ℂ → ℂ) (hg : Differentiable ℂ g) (Y z : ℂ) :
    (∫ s : ℝ in (0)..1, g (Y + z/2*(1-(s : ℂ)^2))) -
      z * (∫ s : ℝ in (0)..1, (s : ℂ)^2 * deriv g (Y+z/2*(1-(s : ℂ)^2))) = g Y := by
  let F (s : ℝ) := g (Y + z/2*(1-(s : ℂ)^2))
  let Q (s : ℝ) := (s : ℂ)^2 * deriv g (Y + z/2*(1-(s : ℂ)^2))
  have hc : Continuous g := hg.continuous
  have hc' : Continuous (deriv g) := continuous_iff_continuousAt.mpr
    (fun w => ((hg.analyticAt w).deriv).continuousAt)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hQ : Continuous Q := by dsimp [Q]; fun_prop
  have hp (s : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ) * F t) (F s-z*Q s) s := by
    have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
    convert hcast.mul (kernelPath_hasDerivAt g hg Y z s) using 1 <;>
      dsimp only [F,Q,Pi.mul_apply] <;> ring
  have hFi : IntervalIntegrable F volume 0 1 := hF.intervalIntegrable 0 1
  have hQi : IntervalIntegrable (fun s => z * Q s) volume 0 1 :=
    (continuous_const.mul hQ).intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun s _ => hp s) (hFi.sub hQi)
  simp only [F, Complex.ofReal_one, one_pow, sub_self, mul_zero, add_zero, one_mul,
    Complex.ofReal_zero, zero_mul, sub_zero] at hFTC
  rw [intervalIntegral.integral_sub hFi hQi, intervalIntegral.integral_const_mul] at hFTC
  exact hFTC

end WP.Analysis
