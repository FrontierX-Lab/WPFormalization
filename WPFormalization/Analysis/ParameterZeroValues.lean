import WPFormalization.Analysis.ParameterIdentities
import WPFormalization.Analysis.KernelZeroValues

/-! The original action, J, density and beta at Y=0, with exact constants.
These are evaluations of the original infimum/integral definitions, not
new endpoint definitions or an asymptotic normalization assumption.
-/
noncomputable section
namespace WP
open MeasureTheory Set Filter
open scoped Topology
lemma action_zero_value : action 0 = Real.pi/4 := by
  unfold action
  rw [T_zero_value,action_integral_kernel 0 (Real.pi^2/4) (by positivity)]
  simp only [sub_zero,Complex.ofReal_zero]
  rw [show (2*(Real.pi^2/4) : ℝ) = Real.pi^2/2 by ring]
  have hH : H 0 ((Real.pi^2/2 : ℝ) : ℂ) = ((3/Real.pi^2 : ℝ) : ℂ) := by
    rw [H_zero_pi_value]
    push_cast
    rfl
  rw [hH,Complex.ofReal_re,sqrt_pi_sq_quarter]
  field_simp [Real.pi_ne_zero]
lemma J_zero_value : J 0 = 1/2 := by
  rw [J_action_identity 0 ⟨le_rfl,y₀_pos⟩,action_zero_value]
  have hDel : Delta 0 = Real.pi^2/4 := by simp only [Delta,T_zero_value,sub_zero]
  rw [hDel,sqrt_pi_sq_quarter]
  have hX : XR 0 = 0 := by simp [XR,X]
  rw [hX,zero_add]
  field_simp [Real.pi_ne_zero]
  ring
lemma density_zero_value : density 0 = 0 := by simp [density,XR,X]
lemma beta_zero_value : beta 0 = 0 := by simp [beta,XR,X]


end WP
