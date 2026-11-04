import WPFormalization.Analysis.RatioSaddleCurvature
import WPFormalization.Analysis.VolumeProfileRegular
import WPFormalization.Volumes.BoundaryTiltContinuity
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

lemma connected_variance_formula (x : ℝ) (hx : x ∈ Ioo 0 xCritical) :
    0 < Psi x ∧ ∃ b : ℝ, 1/3 ≤ b ∧ b ≤ 1 ∧ euler Psi x=Psi x*(1+b*Psi x) := by
  let Y := inverseY x
  have hY : Y ∈ Ico 0 y₀ := (inverseY_branch x ⟨hx.1.le,hx.2⟩).1
  have hXY : XR Y=x := (inverseY_branch x ⟨hx.1.le,hx.2⟩).2
  have hY0 : Y≠0 := by
    intro hz
    rw [hz,XR_zero] at hXY
    linarith [hx.1]
  have hYi : Y ∈ Ioo 0 y₀ := ⟨lt_of_le_of_ne hY.1 hY0.symm,hY.2⟩
  have hp := Analysis.ratioSaddle_mean_pos Y hYi
  rw [hXY] at hp
  refine ⟨hp,Analysis.ratioSaddleDefect Y,Analysis.ratioSaddleDefect_lower Y hY,?_,?_⟩
  · have hA := Analysis.marked_A_pos Y ⟨hY.1,hY.2.le⟩
    have ht := Analysis.T_deriv_neg_interior Y hY
    have htheta := Analysis.Theta_eq_neg_two_T_deriv Y hY
    unfold Analysis.ratioSaddleDefect Theta
    rw [htheta]
    nlinarith
  · simpa only [hXY] using Analysis.ratioSaddle_variance_formula Y hY

lemma connected_variance_upper (x : ℝ) (hx : x ∈ Ioo 0 xCritical) :
    euler Psi x ≤ Psi x*(1+Psi x) := by
  obtain ⟨hp,b,hb,hb1,hv⟩ := connected_variance_formula x hx
  rw [hv]
  nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (sq_nonneg (Psi x))]

lemma connected_variance_scale_bound (h x : ℝ) (hh : 0 < h)
    (hx : x ∈ Ioo 0 xCritical) :
    min h (h*Psi x)*(1+Psi x)^2 ≤ 12*(h*euler Psi x) := by
  obtain ⟨hp,b,hb,hb1,hv⟩ := connected_variance_formula x hx
  have hv1 : Psi x ≤ euler Psi x := BoundaryConvolution.boundary_variance_ge_mean x hx
  have hv2 : (Psi x)^2 ≤ 3*euler Psi x := by
    rw [hv]
    nlinarith [mul_nonneg (by linarith : 0≤b-1/3) (sq_nonneg (Psi x))]
  by_cases hm : Psi x ≤ 1
  · rw [min_eq_right (by nlinarith : h*Psi x≤h)]
    have hs : (1+Psi x)^2 ≤ 4 := by nlinarith
    have ht := mul_le_mul_of_nonneg_left hs (mul_nonneg hh.le hp.le)
    nlinarith [mul_le_mul_of_nonneg_left hv1 hh.le]
  · rw [min_eq_left (by nlinarith : h≤h*Psi x)]
    have hs : (1+Psi x)^2 ≤ 4*(Psi x)^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hs hh.le).trans (by nlinarith [mul_le_mul_of_nonneg_left hv2 hh.le])

/-- Reciprocal mean compactification: its derivative in log x has norm <=1.
This controls relative changes even when the physical coordinate approaches xc. -/
lemma connected_reciprocal_mean_log_hasDerivAt (u : ℝ)
    (hu : Real.exp u < xCritical) :
    HasDerivAt (fun v : ℝ => (1+Psi (Real.exp v))⁻¹)
      (-(euler Psi (Real.exp u))/(1+Psi (Real.exp u))^2) u := by
  have hx : Real.exp u ∈ Ioo 0 xCritical := ⟨Real.exp_pos _,hu⟩
  have hp := (connected_variance_formula _ hx).1
  have hd := ((hasDerivAt_const (x := Real.exp u) (1:ℝ)).add
    (Analysis.Psi_analyticAt_interior _ ⟨hx.1.le,hx.2⟩).differentiableAt.hasDerivAt).inv (by change 1+Psi (Real.exp u)≠0;linarith)
  have ht := hd.comp u (Real.hasDerivAt_exp u)
  convert ht using 1
  · rfl
  · simp only [Pi.add_apply,WP.euler,zero_add]
    ring

lemma connected_reciprocal_mean_log_deriv_bound (u : ℝ)
    (hu : Real.exp u < xCritical) :
    |deriv (fun v : ℝ => (1+Psi (Real.exp v))⁻¹) u| ≤ 1 := by
  have hx : Real.exp u ∈ Ioo 0 xCritical := ⟨Real.exp_pos _,hu⟩
  have hp := (connected_variance_formula _ hx).1
  have hv := connected_variance_upper _ hx
  have hv0 : 0≤euler Psi (Real.exp u) := (BoundaryConvolution.boundary_variance_ge_mean _ hx).trans' hp.le
  rw [(connected_reciprocal_mean_log_hasDerivAt u hu).deriv,abs_div,abs_neg,
    abs_of_nonneg hv0,abs_of_nonneg (sq_nonneg _)]
  apply (div_le_one (sq_pos_of_pos (by linarith : 0<1+Psi (Real.exp u)))).mpr
  nlinarith

lemma connected_reciprocal_mean_log_lipschitz (x y : ℝ)
    (hx : x ∈ Ioo 0 xCritical) (hy : y ∈ Ioo 0 xCritical) :
    |(1+Psi y)⁻¹-(1+Psi x)⁻¹| ≤ |Real.log y-Real.log x| := by
  let f : ℝ→ℝ := fun u => (1+Psi (Real.exp u))⁻¹
  have hs : ∀ u ∈ Iio (Real.log xCritical), Real.exp u < xCritical := by
    intro u hu
    exact (Real.exp_lt_exp.mpr hu).trans_eq (Real.exp_log Analysis.xCritical_pos_parameter)
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Iio (Real.log xCritical))
    (C := 1) (fun u hu => (connected_reciprocal_mean_log_hasDerivAt u (hs u hu)).differentiableAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using connected_reciprocal_mean_log_deriv_bound u (hs u hu))
    (convex_Iio _) (Real.log_lt_log hx.1 hx.2) (Real.log_lt_log hy.1 hy.2)
  simpa only [f,Real.exp_log hx.1,Real.exp_log hy.1,Real.norm_eq_abs,one_mul] using hh

end WP.TightConnected
