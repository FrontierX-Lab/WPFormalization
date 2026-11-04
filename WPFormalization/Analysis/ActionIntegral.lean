import WPFormalization.Analysis.StationaryIntegral

/-! Exact action and J integral identities for arbitrary real Y<T.
The action integral is transformed by the same quadratic substitution as the
stationary integral. Integration by parts for XR(T-(T-Y)s²) proves the J/action
relation without assuming a stationary equation, positivity, or a root branch.
-/
noncomputable section
namespace WP
open MeasureTheory Set
lemma H_real_integral (Y z : ℝ) :
    (H Y z).re = 3*∫ s : ℝ in (0)..1, s^2*a (Y+z/2*(1-s^2)) := by
  have hc : Continuous (deriv X) := by
    simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
  have hi : IntervalIntegrable
      (fun s : ℝ => (s : ℂ)^2*deriv X ((Y : ℂ)+(z : ℂ)/2*(1-(s : ℂ)^2))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold H
  have hthree : (3 : ℂ).re = 3 := by norm_num
  have hthreeIm : (3 : ℂ).im = 0 := by norm_num
  rw [Complex.mul_re,hthree,hthreeIm,zero_mul,sub_zero]
  congr 1
  change Complex.reCLM (∫ s : ℝ in (0)..1,
    (s : ℂ)^2*deriv X ((Y : ℂ)+(z : ℂ)/2*(1-(s : ℂ)^2))) = _
  rw [← Complex.reCLM.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro s hs
  have he : (Y : ℂ)+(z : ℂ)/2*(1-(s : ℂ)^2) = ((Y+z/2*(1-s^2) : ℝ) : ℂ) := by push_cast; ring
  change ((s : ℂ)^2*deriv X ((Y : ℂ)+(z : ℂ)/2*(1-(s : ℂ)^2))).re = _
  have hsre : ((s : ℂ)^2).re = s^2 := by norm_cast
  have hsim : ((s : ℂ)^2).im = 0 := by rw [← Complex.ofReal_pow] <;> rfl
  rw [Complex.mul_re,hsre,hsim,zero_mul,sub_zero,he]
  rfl

lemma action_integral_kernel (Y T : ℝ) (hYT : Y < T) :
    (∫ v in Y..T, a v*Real.sqrt (T-v)) =
      (2/3 : ℝ)*(T-Y)*Real.sqrt (T-Y)*(H Y ((2*(T-Y) : ℝ) : ℂ)).re := by
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
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun v => a v*Real.sqrt (T-v)) hf (fun s hs => hder s) hnonpos
  have hleft : (∫ s : ℝ in (0)..1, ((fun v => a v*Real.sqrt (T-v)) ∘ f) s*f' s) =
      -2*D*Real.sqrt D*(∫ s : ℝ in (0)..1, s^2*a (T-D*s^2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro s hs
    have hs0 : 0 < s := hs.1
    have hsqrt : Real.sqrt (T-(T-D*s^2)) = Real.sqrt D*s := by
      rw [show T-(T-D*s^2) = D*s^2 by ring, Real.sqrt_mul hD.le,
        Real.sqrt_sq_eq_abs,abs_of_pos hs0]
    dsimp [Function.comp_def,f,f']
    rw [hsqrt]
    ring
  have hend : f 0 = T ∧ f 1 = Y := by dsimp [f,D]; constructor <;> ring
  rw [hleft,hend.1,hend.2,intervalIntegral.integral_symm (a := Y) (b := T)] at hchange
  have hkernel : (H Y ((2*D : ℝ) : ℂ)).re = 3*∫ s : ℝ in (0)..1, s^2*a (T-D*s^2) := by
    rw [H_real_integral]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    congr 2
    dsimp [D]
    ring
  dsimp [D] at hchange hkernel
  rw [hkernel]
  linarith
lemma action_integral_square (Y T : ℝ) (hYT : Y < T) :
    (∫ v in Y..T, a v*Real.sqrt (T-v)) =
      2*(T-Y)*Real.sqrt (T-Y)*(∫ s : ℝ in (0)..1, s^2*a (T-(T-Y)*s^2)) := by
  rw [action_integral_kernel Y T hYT,H_real_integral]
  have he : (∫ s : ℝ in (0)..1, s^2*a (Y+(2*(T-Y))/2*(1-s^2))) =
      ∫ s : ℝ in (0)..1, s^2*a (T-(T-Y)*s^2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    congr 2
    ring
  rw [he]
  ring

lemma J_action_integral (Y T : ℝ) (hYT : Y < T) :
    (∫ s : ℝ in (0)..1, XR (T-(T-Y)*s^2)) =
      XR Y+(∫ v in Y..T, a v*Real.sqrt (T-v))/Real.sqrt (T-Y) := by
  let D := T-Y
  have hD : 0 < D := sub_pos.mpr hYT
  let B : ℝ → ℝ := fun s => XR (T-D*s^2)
  let B' : ℝ → ℝ := fun s => -2*D*s*a (T-D*s^2)
  have hx (x : ℝ) : HasDerivAt XR (a x) x :=
    (X_differentiable (x : ℂ)).hasDerivAt.real_of_complex
  have hBder (s : ℝ) : HasDerivAt B (B' s) s := by
    have hin : HasDerivAt (fun s : ℝ => T-D*s^2) (-2*D*s) s := by
      convert (((hasDerivAt_id s).pow 2).const_mul D).const_sub T using 1
      · rfl
      · dsimp; ring
    convert (hx (T-D*s^2)).comp s hin using 1
    · rfl
    · dsimp [B']; ring
  have hc : Continuous (deriv X) := by
    simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
  have ha : Continuous a := Complex.continuous_re.comp (hc.comp Complex.continuous_ofReal)
  have hBp : IntervalIntegrable B' volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp [B']
    fun_prop
  have hib := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := B) (u' := B') (v := fun s : ℝ => s) (v' := fun _ => 1)
    (fun s hs => hBder s) (fun s hs => hasDerivAt_id s) hBp
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1)
  simp only [mul_one,mul_zero,sub_zero] at hib
  have hB1 : B 1 = XR Y := by
    dsimp [B,D]
    congr 1
    ring
  have hi : (∫ s : ℝ in (0)..1, B' s*s) =
      -2*D*(∫ s : ℝ in (0)..1, s^2*a (T-D*s^2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  rw [hB1,hi] at hib
  have hact : (∫ v in Y..T, a v*Real.sqrt (T-v))/Real.sqrt (T-Y) =
      2*D*(∫ s : ℝ in (0)..1, s^2*a (T-D*s^2)) := by
    rw [action_integral_square Y T hYT]
    have hs : Real.sqrt (T-Y) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hYT))
    dsimp [D]
    field_simp [hs]
  rw [hact]
  dsimp [B] at hib
  linarith

end WP
