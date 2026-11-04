import WPFormalization.Analysis.GaussianModelRemainder
/-! A common positive order window absorbs Gaussian polynomial tails and supplies the native linear-order condition. -/
noncomputable section
namespace WP.Analysis
lemma exists_gaussian_outer_window (D a:ℝ) (hD:1≤D) (ha:0<a) :
    ∃c:ℝ,0<c ∧ c≤1 ∧ 2*c*Real.log D≤a/2 := by
  have hlog:0≤Real.log D:=Real.log_nonneg hD
  let c:ℝ:=min 1 (a/(8*(Real.log D+1)))
  have hc:0<c:=lt_min zero_lt_one (div_pos ha (by positivity))
  have hc1:c≤1:=min_le_left _ _
  have hcr:c≤a/(8*(Real.log D+1)):=min_le_right _ _
  have hmul:c*(8*(Real.log D+1))≤a:=(le_div_iff₀ (by positivity)).mp hcr
  exact ⟨c,hc,hc1,by nlinarith[mul_nonneg hc.le hlog]⟩

lemma gaussian_order_small_of_sqrt_window (h c:ℝ) (K:ℕ)
    (hh:256≤h) (hc:c≤1) (hK:(K:ℝ)≤c*Real.sqrt h) :
    8*((K:ℝ)+1)≤h := by
  have hh0:0≤h:=by linarith
  have hs:0≤Real.sqrt h:=Real.sqrt_nonneg h
  have hs16:16≤Real.sqrt h:=by
    have he:=Real.sqrt_le_sqrt hh
    norm_num at he
    exact he
  have hK':(K:ℝ)≤Real.sqrt h:=hK.trans (mul_le_of_le_one_left hs hc)
  have hsq:=Real.sq_sqrt hh0
  nlinarith
end WP.Analysis
