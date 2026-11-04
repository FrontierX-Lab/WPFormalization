import WPFormalization.Analysis.ParameterIdentities
/-! The exact action normalization of the actual H kernel at its first root.
The original stationary/action integral substitution and r=2Delta give the
sqrt(2) factor. This base module does not import Marked. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma normalized_kernel_action (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    A Y*a Y*Real.rpow (r Y) (3/2:ℝ) = Real.sqrt 2*WP.action Y := by
  have ha := WP.a_pos Y hY
  have hD := WP.Delta_pos Y hY
  have hr := (WP.stationary_root_proof Y hY).2.2.2
  have hrpos := WP.r_pos Y hY
  have hRe : (H (Y:ℂ) (r Y:ℂ)/(a Y:ℂ)).re = (H (Y:ℂ) (r Y:ℂ)).re/a Y := by
    simp only [div_eq_mul_inv,← Complex.ofReal_inv,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have hA : A Y*a Y = (H (Y:ℂ) (r Y:ℂ)).re/3 := by
    rw [A,barH,if_neg (ne_of_lt hY.2),mul_one,hRe]
    field_simp [ha.ne'] <;> ring
  have hp : Real.rpow (r Y) (3/2:ℝ) = r Y*Real.sqrt (r Y) := by
    rw [Real.rpow_eq_pow,show (3/2:ℝ) = 1+(1/2:ℝ) by ring,
      Real.rpow_add hrpos,Real.rpow_one,← Real.sqrt_eq_rpow]
  have hI : WP.action Y = (2/3:ℝ)*WP.Delta Y*Real.sqrt (WP.Delta Y)*
      (H (Y:ℂ) ((2*WP.Delta Y:ℝ):ℂ)).re := by
    have ht : Y < WP.T Y := lt_trans hY.2 (WP.stationary_root_proof Y hY).1.1
    simpa only [WP.action,WP.Delta] using WP.action_integral_kernel Y (WP.T Y) ht
  rw [hA,hp,hI,hr,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  ring
end WP.Analysis
