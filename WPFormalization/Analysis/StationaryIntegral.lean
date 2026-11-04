import WPFormalization.Statements.Kernels

/-! Actual Abel-type stationary integrals and their kernel representations.
The substitution v=T-(T-Y)s² is proved with Mathlib's monotone change of
variables theorem. Equality on the open integration interval handles the
single endpoint at which the pulled-back square-root denominator vanishes.
No formal definition of the stationary parameter or any root selection is
assumed in these integral identities.
-/
noncomputable section
namespace WP
open MeasureTheory Set
lemma K_real_integral (Y z : ℝ) :
    (K Y z).re = ∫ s : ℝ in (0)..1, a (Y+z/2*(1-s^2)) := by
  have hc : Continuous (deriv X) := by
    simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
  have hi : IntervalIntegrable
      (fun s : ℝ => deriv X ((Y : ℂ)+(z : ℂ)/2*(1-(s : ℂ)^2))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  change Complex.reCLM (∫ s : ℝ in (0)..1,
    deriv X ((Y : ℂ)+(z : ℂ)/2*(1-(s : ℂ)^2))) = _
  rw [← Complex.reCLM.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro s hs
  have he : (Y : ℂ)+(z : ℂ)/2*(1-(s : ℂ)^2) = ((Y+z/2*(1-s^2) : ℝ) : ℂ) := by
    push_cast
    ring
  change (deriv X ((Y : ℂ)+(z : ℂ)/2*(1-(s : ℂ)^2))).re = _
  rw [he]
  rfl

lemma stationary_integral_kernel (Y T : ℝ) (hYT : Y < T) :
    (∫ v in Y..T, a v/Real.sqrt (T-v)) =
      2*Real.sqrt (T-Y)*(K Y ((2*(T-Y) : ℝ) : ℂ)).re := by
  let D := T-Y
  have hD : 0 < D := sub_pos.mpr hYT
  let f : ℝ → ℝ := fun s => T-D*s^2
  let f' : ℝ → ℝ := fun s => -2*D*s
  have hf : ContinuousOn f (uIcc (0 : ℝ) 1) := by dsimp [f]; fun_prop
  have hder (s : ℝ) : HasDerivAt f (f' s) s := by
    dsimp [f,f']
    convert (((hasDerivAt_id s).pow 2).const_mul D).const_sub T using 1
    · rfl
    · dsimp
      ring
  have hnonpos : ∀ s ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), f' s ≤ 0 := by
    intro s hs
    simp only [min_eq_left zero_le_one,max_eq_right zero_le_one] at hs
    dsimp [f']
    nlinarith [hs.1]
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun v => a v/Real.sqrt (T-v)) hf (fun s hs => hder s) hnonpos
  have hleft : (∫ s : ℝ in (0)..1, ((fun v => a v/Real.sqrt (T-v)) ∘ f) s*f' s) =
      -2*Real.sqrt D*(∫ s : ℝ in (0)..1, a (T-D*s^2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro s hs
    have hs0 : 0 < s := hs.1
    have hsqrt : Real.sqrt (T-(T-D*s^2)) = Real.sqrt D*s := by
      rw [show T-(T-D*s^2) = D*s^2 by ring, Real.sqrt_mul hD.le,
        Real.sqrt_sq_eq_abs,abs_of_pos hs0]
    have hroot : Real.sqrt D ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hD)
    have hsq := Real.sq_sqrt hD.le
    dsimp [Function.comp_def,f,f']
    rw [hsqrt]
    field_simp [hroot,ne_of_gt hs0]
    rw [hsq]
    ring
  have hend : f 0 = T ∧ f 1 = Y := by dsimp [f,D]; constructor <;> ring
  rw [hleft,hend.1,hend.2,intervalIntegral.integral_symm (a := Y) (b := T)] at hchange
  have hkernel : (K Y ((2*D : ℝ) : ℂ)).re = ∫ s : ℝ in (0)..1, a (T-D*s^2) := by
    rw [K_real_integral]
    apply intervalIntegral.integral_congr
    intro s hs
    congr 1
    dsimp [D]
    ring
  rw [← hkernel] at hchange
  dsimp [D] at hchange
  linarith

open MeasureTheory Set
lemma stationary_intervalIntegrable (Y T : ℝ) (hYT : Y < T) :
    IntervalIntegrable (fun v => a v/Real.sqrt (T-v)) volume Y T := by
  let D := T-Y
  have hD : 0 < D := sub_pos.mpr hYT
  let f : ℝ → ℝ := fun s => T-D*s^2
  let f' : ℝ → ℝ := fun s => -2*D*s
  have hf : ContinuousOn f (uIcc (0 : ℝ) 1) := by dsimp [f]; fun_prop
  have hder (s : ℝ) : HasDerivAt f (f' s) s := by
    dsimp [f,f']
    convert (((hasDerivAt_id s).pow 2).const_mul D).const_sub T using 1
    · rfl
    · dsimp; ring
  have hnonpos : ∀ s ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), f' s ≤ 0 := by
    intro s hs
    simp only [min_eq_left zero_le_one,max_eq_right zero_le_one] at hs
    dsimp [f']
    nlinarith [hs.1]
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
    (g := fun v => a v/Real.sqrt (T-v)) hf (fun s hs => hder s) hnonpos
  have hc : Continuous (deriv X) := by
    simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
  have ha : Continuous a := Complex.continuous_re.comp (hc.comp Complex.continuous_ofReal)
  have hi : IntervalIntegrable (fun s : ℝ => -2*Real.sqrt D*a (T-D*s^2)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpull : IntervalIntegrable
      (fun s => ((fun v => a v/Real.sqrt (T-v)) ∘ f) s*f' s) volume 0 1 := by
    apply hi.congr_uIoo
    intro s hs
    rw [uIoo_of_le zero_le_one] at hs
    have hs0 : 0 < s := hs.1
    have hsqrt : Real.sqrt (T-(T-D*s^2)) = Real.sqrt D*s := by
      rw [show T-(T-D*s^2) = D*s^2 by ring, Real.sqrt_mul hD.le,
        Real.sqrt_sq_eq_abs,abs_of_pos hs0]
    have hroot : Real.sqrt D ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hD)
    have hsq := Real.sq_sqrt hD.le
    dsimp [Function.comp_def,f,f']
    rw [hsqrt]
    field_simp [hroot,ne_of_gt hs0]
    rw [hsq]
  have he := hiff.mp hpull
  have hend : f 0 = T ∧ f 1 = Y := by dsimp [f,D]; constructor <;> ring
  rw [hend.1,hend.2] at he
  exact he.symm

end WP
