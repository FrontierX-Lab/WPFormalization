import WPFormalization.Analysis.RatioSaddleCurvature
import WPFormalization.Volumes.PrefactorIntegration

/-! A genuine uniform tilt bound for the original inverse parameter.
The variance is the actual Euler derivative of Psi. Its exact curvature
identity supplies the bound through both degenerate endpoints. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology

lemma inverse_parameter_tilt_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Ioo (0:ℝ) xCritical,
      |x*deriv inverseY x/Real.sqrt (euler Psi x)| ≤ C := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    Analysis.A_continuousOn_closed_parameter
  let B : ℝ := max 1 M
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hAB : ∀ Y ∈ Ico (0:ℝ) y₀, 0 < A Y ∧ A Y ≤ B := by
    intro Y hY
    exact ⟨Analysis.marked_A_pos Y ⟨hY.1,hY.2.le⟩,
      (le_abs_self _).trans ((hM Y ⟨hY.1,hY.2.le⟩).trans (le_max_right _ _))⟩
  let R : ℝ := Real.pi^2/2
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨2*(B*R),by positivity,?_⟩
  intro x hx
  let Y : ℝ := inverseY x
  have hY : Y ∈ Ico (0:ℝ) y₀ := (inverseY_branch x ⟨hx.1.le,hx.2⟩).1
  have hXY : XR Y = x := (inverseY_branch x ⟨hx.1.le,hx.2⟩).2
  have hY0 : Y ≠ 0 := by
    intro hz
    have hh := hXY
    rw [hz,XR_zero] at hh
    linarith [hx.1]
  have hYi : Y ∈ Ioo (0:ℝ) y₀ := ⟨lt_of_le_of_ne hY.1 hY0.symm,hY.2⟩
  have hψ := Analysis.ratioSaddle_mean_pos Y hYi
  have hv := Analysis.ratioSaddle_variance_pos Y hYi
  rw [hXY] at hψ hv
  have hsq := Analysis.ratioSaddle_mean_square_over_variance Y hYi
  rw [hXY] at hsq
  have hψsq : Psi x^2 ≤ 3*euler Psi x := (div_le_iff₀ hv).mp hsq
  have hroot : 0 < Real.sqrt (euler Psi x) := Real.sqrt_pos.mpr hv
  have hψroot : Psi x ≤ 2*Real.sqrt (euler Psi x) := by
    nlinarith [Real.sq_sqrt hv.le]
  have hr : r Y ≤ R := by
    have hh := Analysis.r_le_pi Y hY
    dsimp [R]
    linarith [hY.1]
  have hAr : 0 ≤ A Y*r Y := (mul_pos (hAB Y hY).1 (r_pos Y hY)).le
  have hArB : A Y*r Y ≤ B*R :=
    mul_le_mul (hAB Y hY).2 hr (r_pos Y hY).le hB.le
  have hxa := Analysis.ratioSaddle_x_over_a Y hY
  rw [hXY] at hxa
  have hnum : x/a Y ≤ 2*(B*R)*Real.sqrt (euler Psi x) := by
    rw [hxa]
    have hh := mul_le_mul_of_nonneg_left hψroot hAr
    have hh' := mul_le_mul_of_nonneg_right hArB (by positivity : 0 ≤ 2*Real.sqrt (euler Psi x))
    nlinarith only [hh,hh']
  rw [(Analysis.inverseY_hasDerivAt_interior x ⟨hx.1.le,hx.2⟩).deriv]
  change |x*(a Y)⁻¹/Real.sqrt (euler Psi x)| ≤ _
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hx.1.le (inv_nonneg.mpr (a_pos Y hY).le)) hroot.le)]
  apply (div_le_iff₀ hroot).mpr
  simpa only [div_eq_mul_inv] using hnum

end WP.BoundaryConvolution
