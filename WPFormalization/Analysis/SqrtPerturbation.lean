import WPFormalization.Analysis.ComplexCharacteristic

/-! Quantitative perturbation bounds for the principal complex square root.
These elementary estimates apply to arbitrary complex w. They isolate the
branch estimates in the kernel comparison, with no assumptions about zeros. -/
noncomputable section
namespace WP.Analysis
lemma complex_sqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  change 0 ≤ (z^(2⁻¹:ℂ)).re
  rw [Complex.cpow_inv_two_re]
  positivity
lemma complex_sqrt_sub_one_norm (w : ℂ) :
    ‖Complex.sqrt (1-w)-1‖ ≤ ‖w‖ := by
  let q := Complex.sqrt (1-w)
  have hq : q^2 = 1-w := complex_sqrt_sq _
  have hre : 0 ≤ q.re := complex_sqrt_re_nonneg _
  have hp : 1 ≤ ‖q+1‖ := by
    have hh := (le_abs_self (q+1).re).trans (Complex.abs_re_le_norm (q+1))
    simp only [Complex.add_re,Complex.one_re] at hh
    linarith
  have he : (q-1)*(q+1) = -w := by linear_combination hq
  have hn := congrArg norm he
  rw [norm_mul,norm_neg] at hn
  calc
    ‖q-1‖ ≤ ‖q-1‖*‖q+1‖ := by nlinarith [norm_nonneg (q-1)]
    _ = ‖w‖ := hn
lemma complex_sqrt_inverse_norm (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖(Complex.sqrt (1-w))⁻¹‖ ≤ 2 := by
  have hb := complex_sqrt_sub_one_norm w
  have ht := norm_sub_norm_le (1:ℂ) (Complex.sqrt (1-w))
  rw [norm_one,norm_sub_rev] at ht
  have hq : (1/2:ℝ) ≤ ‖Complex.sqrt (1-w)‖ := by linarith
  rw [norm_inv]
  exact (inv_le_comm₀ (by positivity) (by norm_num : (0:ℝ)<2)).2 (by linarith)
lemma complex_sqrt_inverse_sub_one_norm (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖(Complex.sqrt (1-w))⁻¹-1‖ ≤ 2*‖w‖ := by
  let q := Complex.sqrt (1-w)
  have hb := complex_sqrt_sub_one_norm w
  have hi := complex_sqrt_inverse_norm w hw
  have hq : q ≠ 0 := by
    intro he
    have hh := congrArg (fun z : ℂ=>‖z-1‖) he
    simp only [zero_sub,norm_neg,norm_one] at hh
    change ‖q-1‖ ≤ ‖w‖ at hb
    rw [hh] at hb
    linarith
  have he : q⁻¹-1 = q⁻¹*(1-q) := by field_simp
  change ‖q⁻¹-1‖ ≤ _
  rw [he,norm_mul,norm_sub_rev]
  exact mul_le_mul hi hb (norm_nonneg _) (by norm_num)
end WP.Analysis
