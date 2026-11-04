import WPFormalization.Analysis.HKernelPositivity
import WPFormalization.Analysis.CoefficientScaling
import WPFormalization.Statements.IntersectionInterface

/-! Positivity of the actual harmonic coefficients. The interior proof currently
uses the proved H-kernel positivity and the still-unfinished r_pos/kernel_zeros input;
the critical endpoint proof is independent of those declarations. -/
noncomputable section
namespace WP
open Analysis

lemma harmonicCoeff_pos_interior (Y : ℝ) (h m : ℕ) (hh : 0 < h)
    (hY : Y ∈ Set.Ico 0 y₀) : 0 < harmonicCoeff Y h m := by
  have he : (fun z => (barH Y z)⁻¹^h) =
      fun z => (Complex.ofReal ((a Y)^h))*((H Y ((r Y : ℂ)*z))⁻¹^h) := by
    funext z
    simp [barH,ne_of_lt hY.2,div_eq_mul_inv,mul_pow]
  unfold harmonicCoeff
  rw [he,realCoeff_const_mul]
  have hs := realCoeff_comp_mul_left (fun z => (H Y z)⁻¹^h) (r Y) m
  rw [hs]
  have hne : H (Y : ℂ) 0 ≠ 0 := by
    rw [H_zero,derivX_ofReal]
    exact_mod_cast a_ne_zero Y hY
  rw [realCoeff_inv_pow_eq_exp (H Y) ((H_differentiable Y).continuous.continuousAt) hne h m]
  exact mul_pos (pow_pos (a_pos Y hY) h)
    (mul_pos (pow_pos (r_pos Y hY) m)
      (H_negative_power_coeff_pos Y hY h (Nat.cast_pos.mpr hh) m))
lemma harmonicCoeff_pos (Y : ℝ) (h m : ℕ) (hh : 0 < h)
    (hY : Y ∈ Set.Icc 0 y₀) : 0 < harmonicCoeff Y h m := by
  by_cases he : Y = y₀
  · subst Y
    have heq : (fun z => (barH y₀ z)⁻¹^h) =
        fun z => (1-(3/5 : ℂ)*z)⁻¹^h := by funext z; simp [barH]
    unfold harmonicCoeff
    rw [heq]
    have hs := realCoeff_comp_mul_left (fun z : ℂ => (1-z)⁻¹^h) (3/5) m
    have hc : ((3/5 : ℝ) : ℂ) = (3/5 : ℂ) := by norm_num
    rw [hc] at hs
    rw [hs]
    exact mul_pos (pow_pos (by norm_num : (0 : ℝ)<3/5) m) (inverseLinear_coeff_pos h m hh)
  · exact harmonicCoeff_pos_interior Y h m hh ⟨hY.1,lt_of_le_of_ne hY.2 he⟩

end WP
