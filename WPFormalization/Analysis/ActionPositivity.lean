import WPFormalization.Analysis.StationaryRoot
import WPFormalization.Analysis.ActionIntegral

/-! Positivity of the actual stationary action.
The normalized integrand has mean zero. Centering its s² weight at the unique
sign change of a(T-(T-Y)s²) gives a continuous nonnegative function, strictly
positive at s=1. This proves action positivity from the original stationary
root and the proved derivative signs, without a canonical-product assumption.
-/
noncomputable section
namespace WP
open MeasureTheory Set
lemma a_hasDerivAt (x : ℝ) : HasDerivAt a ((iteratedDeriv 2 X x).re) x := by
  have hd := ((iteratedDeriv_X_differentiable 1) (x : ℂ)).hasDerivAt.real_of_complex
  change HasDerivAt (fun t : ℝ => (deriv X (t : ℂ)).re) ((iteratedDeriv 2 X x).re) x
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using hd
lemma a_strictAntiOn_pi : StrictAntiOn a (Icc 0 (Real.pi^2/4)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) Analysis.a_continuous.continuousOn
  intro x hx
  rw [(a_hasDerivAt x).deriv]
  have hx' : x ∈ Icc 0 (Real.pi^2/4) := interior_subset hx
  exact (bessel_signs_pi_interval.2.1 x hx').1
lemma K_real_stationary_integral (Y T : ℝ) :
    (K Y ((2*(T-Y) : ℝ) : ℂ)).re = ∫ s : ℝ in (0)..1,a (T-(T-Y)*s^2) := by
  rw [K_real_integral]
  apply intervalIntegral.integral_congr
  intro s hs
  apply congrArg a
  ring
lemma stationary_action_pos (Y T : ℝ) (hY : Y ∈ Ico 0 y₀)
    (hT : T ∈ Ioc y₀ (Real.pi^2/4)) (hroot : K Y ((2*(T-Y) : ℝ) : ℂ) = 0) :
    0 < ∫ v in Y..T,a v*Real.sqrt (T-v) := by
  let D := T-Y
  let q := (T-y₀)/D
  have hYT : Y < T := lt_trans hY.2 hT.1
  have hD : 0 < D := sub_pos.mpr hYT
  let f : ℝ → ℝ := fun s => (s^2-q)*a (T-D*s^2)
  have haCont : Continuous a := Analysis.a_continuous
  have hf : Continuous f := by dsimp [f]; exact (by fun_prop)
  have hnonneg (s : ℝ) (hs : s ∈ Ioc 0 1) : 0 ≤ f s := by
    have hs2 : 0 ≤ s^2 ∧ s^2 ≤ 1 := ⟨sq_nonneg s,by nlinarith [hs.1,hs.2]⟩
    have hv0 : 0 ≤ T-D*s^2 := by dsimp [D] at *; nlinarith [hY.1]
    have hvtop : T-D*s^2 ≤ Real.pi^2/4 := by nlinarith [hT.2]
    dsimp [f]
    by_cases hv : T-D*s^2 ≤ y₀
    · have hcoef : 0 ≤ s^2-q := by dsimp [q]; rw [sub_nonneg,div_le_iff₀ hD]; nlinarith
      have ha : 0 ≤ a (T-D*s^2) := by
        by_cases he : T-D*s^2 = y₀
        · rw [he,a_y₀_zero]
        · exact (a_pos _ ⟨hv0,lt_of_le_of_ne hv he⟩).le
      exact mul_nonneg hcoef ha
    · have hvgt : y₀ < T-D*s^2 := lt_of_not_ge hv
      have hcoef : s^2-q ≤ 0 := by dsimp [q]; rw [sub_nonpos,le_div_iff₀ hD]; nlinarith
      have ha := a_strictAntiOn_pi ⟨y₀_pos.le,le_trans hT.1.le hT.2⟩ ⟨hv0,hvtop⟩ hvgt
      rw [a_y₀_zero] at ha
      exact mul_nonneg_of_nonpos_of_nonpos hcoef ha.le
  have hpositive : 0 < ∫ s : ℝ in (0)..1,f s := by
    apply intervalIntegral.integral_pos zero_lt_one hf.continuousOn hnonneg
    refine ⟨1,⟨zero_le_one,le_rfl⟩,?_⟩
    have hq : 0 < 1-q := by dsimp [q]; rw [sub_pos,div_lt_one hD]; dsimp [D]; linarith [hY.2]
    have he : T-D*1^2 = Y := by dsimp [D]; ring
    dsimp [f]
    rw [he]
    exact mul_pos (by simpa using hq) (a_pos Y hY)
  have hQ : (∫ s : ℝ in (0)..1,a (T-D*s^2)) = 0 := by
    rw [← K_real_stationary_integral Y T,hroot,Complex.zero_re]
  have hi₁ : IntervalIntegrable (fun s : ℝ => s^2*a (T-D*s^2)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi₂ : IntervalIntegrable (fun s : ℝ => q*a (T-D*s^2)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he : (∫ s : ℝ in (0)..1,f s) = ∫ s : ℝ in (0)..1,s^2*a (T-D*s^2) := by
    simp only [f,sub_mul]
    rw [intervalIntegral.integral_sub hi₁ hi₂,intervalIntegral.integral_const_mul,hQ,mul_zero,sub_zero]
  rw [he] at hpositive
  rw [action_integral_square Y T hYT]
  exact mul_pos (mul_pos (mul_pos (by norm_num) hD) (Real.sqrt_pos.mpr hD)) hpositive
end WP
