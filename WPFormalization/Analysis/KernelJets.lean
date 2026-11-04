import WPFormalization.Analysis.Taylor
import WPFormalization.Analysis.CoefficientScaling
import WPFormalization.Statements.Kernels

/-! Analyticity and reality of normalized kernel jets. These use only the
proved entire integral kernels and real Bessel jets, not their zero estimates. -/
noncomputable section
namespace WP
open Analysis

lemma barH_differentiable (Y : ℝ) : Differentiable ℂ (barH Y) := by
  by_cases h : Y = y₀
  · rw [show barH Y = (fun z : ℂ => 1-(3/5 : ℂ)*z) by funext z; simp [barH,h]]
    fun_prop
  · rw [show barH Y = (fun z : ℂ => H Y ((r Y : ℂ)*z)/(a Y : ℂ)) by
      funext z; simp [barH,h]]
    exact ((H_differentiable Y).comp (by fun_prop)).div_const _

lemma barH_zero (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) : barH Y 0 = 1 := by
  by_cases h : Y = y₀
  · simp [barH,h]
  · have hi : Y ∈ Set.Ico 0 y₀ := ⟨hY.1, lt_of_le_of_ne hY.2 h⟩
    have ha : (a Y : ℂ) ≠ 0 := by exact_mod_cast a_ne_zero Y hi
    simp [barH,h,H_zero,derivX_ofReal,ha]

lemma barH_realCoefficients (Y : ℝ) : RealCoefficients (barH Y) := by
  by_cases h : Y = y₀
  · have he : barH Y = (fun z : ℂ => 1-(3/5 : ℂ)*z) := by
      funext z; simp [barH,h]
    have hj : taylor (barH Y) = PowerSeries.C 1-PowerSeries.C (3/5 : ℂ)*PowerSeries.X := by
      rw [he, taylor_sub (f := fun _ : ℂ => 1) (g := fun z : ℂ => (3/5 : ℂ)*z)
        analyticAt_const (analyticAt_const.mul analyticAt_id),
        taylor_const, taylor_const_mul (3/5 : ℂ) (fun z : ℂ => z), taylor_id]
    intro n
    change (coeff (barH Y) n).im = 0
    rw [← taylor_coeff, hj]
    simp only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C, PowerSeries.coeff_X]
    split_ifs <;> norm_num
  · have he : barH Y = (fun z : ℂ => H Y ((r Y : ℂ)*z)/(a Y : ℂ)) := by
      funext z; simp [barH,h]
    intro n
    change (iteratedDeriv n (barH Y) 0/(n.factorial : ℂ)).im = 0
    rw [he,iteratedDeriv_div_const,Analysis.iteratedDeriv_comp_mul_left,mul_zero,
      iteratedDeriv_H_zero]
    have hx : iteratedDeriv (n+1) X (Y : ℂ) =
        ((iteratedDeriv (n+1) X (Y : ℂ)).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using iteratedDeriv_X_im_ofReal (n+1) Y
    rw [hx]
    have hc : (r Y : ℂ)^n*(3*((n.factorial : ℂ)/(oddFactorial (n+1) : ℂ))*
        ((iteratedDeriv (n+1) X (Y : ℂ)).re : ℂ))/(a Y : ℂ)/(n.factorial : ℂ) =
        ((r Y^n*(3*((n.factorial : ℝ)/(oddFactorial (n+1) : ℝ)))*
          (iteratedDeriv (n+1) X (Y : ℂ)).re/a Y/(n.factorial : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hc]
    rfl

end WP
