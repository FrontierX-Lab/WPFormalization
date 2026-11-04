import WPFormalization.Statements.Parameter
import WPFormalization.Analysis.ParameterZeroValues
/-! Exact normalization of the integral boundary factor at the zero parameter.
The removable X(v)/v value is handled before the integral is evaluated. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory
lemma varpi_zero_value : WP.varpi 0 = 1 := by
  have hT : WP.T 0 = Real.pi^2/4 := WP.T_zero_value
  have hD : WP.Delta 0 = Real.pi^2/4 := by simp only [WP.Delta,hT,sub_zero]
  have hpi : (Real.pi^2/4:ℝ) ≠ 0 := by positivity
  have he (s : ℝ) :
      (1-s^2)*WP.Xdiv (Real.pi^2/4-Real.pi^2/4*s^2) =
        WP.XR (Real.pi^2/4-Real.pi^2/4*s^2)/(Real.pi^2/4) := by
    by_cases hv : Real.pi^2/4-Real.pi^2/4*s^2=0
    · have hs : 1-s^2=0 := by
        apply (mul_eq_zero.mp (show (Real.pi^2/4)*(1-s^2)=0 by nlinarith)).resolve_left hpi
      rw [hs,zero_mul,hv,WP.XR_zero,zero_div]
    · simp only [WP.Xdiv,if_neg hv]
      have hfac : (1-s^2:ℝ) ≠ 0 := by
        intro hs
        apply hv
        nlinarith
      field_simp [Real.pi_ne_zero,hfac]
  have hi : (∫ s : ℝ in (0)..1, (1-s^2)*WP.Xdiv
        (WP.T 0-WP.Delta 0*s^2)) = WP.J 0/(Real.pi^2/4) := by
    rw [WP.J,hT,hD,←intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro s hs
    exact he s
  have hp : Real.rpow (Real.pi^2/4) (3/2:ℝ) = Real.pi^3/8 := by
    rw [Real.rpow_eq_pow,show (3/2:ℝ)=1+(1/2:ℝ) by ring,Real.rpow_add (by positivity),
      Real.rpow_one,←Real.sqrt_eq_rpow,WP.sqrt_pi_sq_quarter]
    ring
  rw [WP.varpi,hi,hD,WP.J_zero_value,WP.action_zero_value,hp]
  have hr : (Real.pi/4)/(Real.pi^3/8)/((1/2)/(Real.pi^2/4)) = (1:ℝ) := by
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [hr,Real.sqrt_one]
end WP.Analysis
