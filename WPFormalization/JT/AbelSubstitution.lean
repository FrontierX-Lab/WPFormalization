import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Abel substitution at the integrable square-root endpoint.  The numerator
is arbitrary and continuous; no Bessel or JT identity is assumed. -/
noncomputable section
namespace WP.JT
open MeasureTheory Set

private lemma abel_change_hasDeriv (e q s : ℝ) :
    HasDerivAt (fun t : ℝ => e + q * (1 - t^2)) (-2*q*s) s := by
  convert (((hasDerivAt_id s).pow 2).const_sub 1).const_mul q |>.const_add e using 1
  all_goals simp only [id_eq, Pi.pow_apply]
  all_goals ring

private lemma abel_change_cancel (f : ℝ → ℝ) (e q s : ℝ) (hq : 0 < q) (hs : 0 < s) :
    (f (e+q*(1-s^2)) / Real.sqrt (e+q-(e+q*(1-s^2)))) * (-2*q*s) =
      (-2*Real.sqrt q) * f (e+q*(1-s^2)) := by
  have he : e+q-(e+q*(1-s^2)) = q*s^2 := by ring
  rw [he, Real.sqrt_mul hq.le, Real.sqrt_sq hs.le]
  have hn : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hsq := Real.sq_sqrt hq.le
  field_simp
  rw [hsq]
  ring

/-- A continuous numerator divided by the endpoint square root is integrable,
including the degenerate interval. -/
theorem abel_intervalIntegrable (f : ℝ → ℝ) (hf : Continuous f)
    (e q : ℝ) (hq : 0 ≤ q) :
    IntervalIntegrable (fun u => f u / Real.sqrt (e+q-u)) volume e (e+q) := by
  rcases eq_or_lt_of_le hq with hzero | hpos
  · subst q
    simp
  have hi : IntervalIntegrable
      (fun s => (f (e+q*(1-s^2)) / Real.sqrt (e+q-(e+q*(1-s^2)))) * (-2*q*s))
      volume 0 1 := by
    have hcont : Continuous (fun s : ℝ => (-2*Real.sqrt q)*f (e+q*(1-s^2))) := by
      exact continuous_const.mul (hf.comp (by fun_prop))
    apply (hcont.intervalIntegrable 0 1).congr_uIoo
    intro s hs
    have hspos : 0 < s := by simpa using hs.1
    exact (abel_change_cancel f e q s hpos hspos).symm
  have he := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
    (a := (0 : ℝ)) (b := 1)
    (f := fun s : ℝ => e+q*(1-s^2)) (f' := fun s => -2*q*s)
    (g := fun u => f u / Real.sqrt (e+q-u))
    (show ContinuousOn (fun s : ℝ => e+q*(1-s^2)) (uIcc 0 1) from (by fun_prop))
    (fun s _ => abel_change_hasDeriv e q s)
    (by intro s hs; have hs0 : 0 ≤ s := le_of_lt (by simpa using hs.1); nlinarith)
  have ht := he.mp hi
  simp only [zero_pow (by norm_num : (2:ℕ)≠0), sub_zero, mul_one, one_pow, sub_self,
    mul_zero, add_zero] at ht
  exact ht.symm

/-- The literal Abel integral after `u = e + q*(1-s²)`. Endpoint values
are handled almost everywhere; the original integral is finite by
`abel_intervalIntegrable`. -/
theorem abel_substitution (f : ℝ → ℝ) (_hf : Continuous f)
    (e q : ℝ) (hq : 0 ≤ q) :
    (∫ u in e..(e+q), f u / Real.sqrt (e+q-u)) =
      2*Real.sqrt q * ∫ s : ℝ in (0)..1, f (e+q*(1-s^2)) := by
  rcases eq_or_lt_of_le hq with hzero | hpos
  · subst q
    simp
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (0 : ℝ)) (b := 1)
    (f := fun s : ℝ => e+q*(1-s^2)) (f' := fun s => -2*q*s)
    (g := fun u => f u / Real.sqrt (e+q-u))
    (show ContinuousOn (fun s : ℝ => e+q*(1-s^2)) (uIcc 0 1) from (by fun_prop))
    (fun s _ => abel_change_hasDeriv e q s)
    (by intro s hs; have hs0 : 0 ≤ s := le_of_lt (by simpa using hs.1); nlinarith)
  have hleft :
      (∫ s : ℝ in (0)..1,
        ((fun u => f u / Real.sqrt (e+q-u)) ∘ (fun s : ℝ => e+q*(1-s^2))) s * (-2*q*s)) =
      (-2*Real.sqrt q) * ∫ s : ℝ in (0)..1, f (e+q*(1-s^2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro s hs
    exact abel_change_cancel f e q s hpos hs.1
  rw [hleft] at he
  simp only [zero_pow (by norm_num : (2:ℕ)≠0), sub_zero, mul_one, one_pow, sub_self,
    mul_zero, add_zero] at he
  rw [intervalIntegral.integral_symm (a := e) (b := e+q)] at he
  linarith
end WP.JT
