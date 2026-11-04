import WPFormalization.Tight.ShiftedPolynomial

noncomputable section
namespace WP.TightSeparating
open Set

/-- Exact physical integration/Jacobian cancellation in original F.3.
The original P^(-k), actual scale alpha^(-2k), and root power r^k
leave exactly 4^(-k). -/
lemma separating_physical_normalization (Y : ℝ) (hY : Y ∈ Ico (0 : ℝ) y₀) (k : ℕ) :
    (r Y)^k / ((2*Real.pi^2)^k * (tightParameterScale Y)^(2*k)) = 1/(4 : ℝ)^k := by
  have hr : r Y ≠ 0 := (r_pos Y hY).ne'
  have ha : tightParameterScale Y ≠ 0 := (tightParameterScale_pos Y hY).ne'
  have hs := tightParameterScale_square Y hY
  have hs' : (2*Real.pi^2)*(tightParameterScale Y)^2 = 4*r Y := by
    have hp : (2*Real.pi^2 : ℝ) ≠ 0 := by positivity
    have hh := (div_eq_div_iff (by norm_num : (4 : ℝ) ≠ 0) hp).mp hs
    nlinarith
  have he : (2*Real.pi^2)^k * (tightParameterScale Y)^(2*k) = (4*r Y)^k := by
    rw [pow_mul,←mul_pow,hs']
  rw [he,mul_pow]
  field_simp

end WP.TightSeparating
