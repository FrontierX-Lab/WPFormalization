import Mathlib

/-! Continuous Frechet derivatives of affine compact-interval parameter integrals.
A compact bound on the displayed derivative permits differentiation under the
integral; its continuous integral yields C¹ jointly in the two complex inputs.
This reusable analytic-calculus result contains no stationary parameter or
kernel-specific assumption.
-/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Metric
open scoped Topology
abbrev ComplexPair := ℂ × ℂ
lemma hasFDerivAt_affineIntegral_prod (q A : ℝ → ℂ)
    (L : ℝ → ComplexPair →L[ℂ] ℂ) (hq : Continuous q) (hA : Continuous A) (hL : Continuous L)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (p : ComplexPair) :
    HasFDerivAt (fun w : ComplexPair => ∫ s : ℝ in (0)..1,q s*g (A s+L s w))
      (∫ s : ℝ in (0)..1,(q s*deriv g (A s+L s p)) • L s) p := by
  let F (w : ComplexPair) (s : ℝ) := q s*g (A s+L s w)
  let F' (w : ComplexPair) (s : ℝ) : ComplexPair →L[ℂ] ℂ :=
    (q s*deriv g (A s+L s w)) • L s
  have hc : Continuous g := hg.continuous
  have hc' : Continuous (deriv g) := continuous_iff_continuousAt.mpr (fun z => ((hg.analyticAt z).deriv).continuousAt)
  have hF (w : ComplexPair) : Continuous (F w) := by dsimp [F]; fun_prop
  have hF' : Continuous (fun r : ComplexPair × ℝ => F' r.1 r.2) := by dsimp [F']; fun_prop
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).bddAbove_image hF'.norm.continuousOn
  have hi : HasFDerivAt (fun w : ComplexPair => ∫ s, F w s ∂volume.restrict (Ioc (0 : ℝ) 1))
      (∫ s,F' p s ∂volume.restrict (Ioc (0 : ℝ) 1)) p := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := F) (F' := F') (bound := fun _ => C) (ball_mem_nhds p zero_lt_one)
    · filter_upwards with w
      exact (hF w).aestronglyMeasurable.restrict
    · exact (hF p).intervalIntegrable 0 1 |>.1
    · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs w hw
      apply hC
      exact ⟨(w,s),⟨mem_closedBall.mpr (le_of_lt (mem_ball.mp hw)),Ioc_subset_Icc_self hs⟩,rfl⟩
    · exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume 0 1).1
    · filter_upwards with s w hw
      dsimp [F,F']
      convert (((hg _).hasDerivAt.hasFDerivAt.comp w
        ((L s).hasFDerivAt.const_add (A s))).const_mul (q s)) using 1 <;>
        first | rfl | (ext v <;> simp [smul_eq_mul] <;> ring)
  simpa only [intervalIntegral.integral_of_le zero_le_one,F,F'] using hi

lemma affineIntegral_prod_contDiff_one (q A : ℝ → ℂ)
    (L : ℝ → ComplexPair →L[ℂ] ℂ) (hq : Continuous q) (hA : Continuous A) (hL : Continuous L)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    ContDiff ℂ 1 (fun w : ComplexPair => ∫ s : ℝ in (0)..1,q s*g (A s+L s w)) := by
  have hc : Continuous (deriv g) := continuous_iff_continuousAt.mpr (fun z => ((hg.analyticAt z).deriv).continuousAt)
  let F' (w : ComplexPair) : ComplexPair →L[ℂ] ℂ :=
    ∫ s : ℝ in (0)..1,(q s*deriv g (A s+L s w)) • L s
  have hF' : Continuous F' := by
    have hj : Continuous (fun r : ComplexPair × ℝ => (q r.2*deriv g (A r.2+L r.2 r.1)) • L r.2) := by fun_prop
    have he := continuous_parametric_integral_of_continuous
      (X := ComplexPair) (Y := ℝ) (E := ComplexPair →L[ℂ] ℂ)
      (f := fun w s => (q s*deriv g (A s+L s w)) • L s) (μ := volume) hj
      (s := Icc (0 : ℝ) 1) isCompact_Icc
    simpa only [F',intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc] using he
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨F',hF',fun w => hasFDerivAt_affineIntegral_prod q A L hq hA hL g hg w⟩
end WP.Analysis
