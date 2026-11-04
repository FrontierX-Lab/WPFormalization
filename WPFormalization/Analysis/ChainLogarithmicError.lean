import WPFormalization.Statements.Basic

/-! Elementary logarithmic conversion of a relative error near one. -/
noncomputable section
namespace WP.Analysis

lemma chain_abs_log_of_relative_error (x δ : ℝ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/2)
    (hx : |x-1| ≤ δ) : |Real.log x| ≤ 2*δ := by
  have hb := abs_le.mp hx
  have hhalf : 1/2 ≤ x := by linarith only [hb.1,hsmall]
  have hpos : 0 < x := by linarith only [hhalf]
  have hinv : x⁻¹ ≤ 1+2*δ := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).mpr
    have hm := mul_nonneg hδ (sub_nonneg.mpr hhalf)
    nlinarith only [hb.1,hm]
  have hu := Real.log_le_sub_one_of_pos hpos
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hl
  exact abs_le.mpr ⟨by linarith only [hl,hinv],by linarith only [hu,hb.2,hδ]⟩

end WP.Analysis
