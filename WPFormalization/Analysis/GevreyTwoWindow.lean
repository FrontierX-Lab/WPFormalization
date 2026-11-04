import WPFormalization.Analysis.GevreyTwoOptimalTruncation
noncomputable section
namespace WP.Analysis
lemma gevreyTwo_cauchy_window (B c₀:ℝ) (hB:0<B) (hc₀:0<c₀):
    ∃c H:ℝ,0<c ∧ c ≤ c₀ ∧ 0<H ∧∀h:ℝ,H ≤ h→∀K:ℕ,
      (K:ℝ) ≤ c*Real.sqrt h→4*B*((K:ℝ)+1)^2 ≤ h:=by
  let c:ℝ:=min c₀ (1/(8*(B+1)))
  have hc:0<c:=lt_min hc₀ (by positivity)
  have hcap:8*(B+1)*c ≤ 1:=by
    have he:=(le_div_iff₀ (by positivity:0<8*(B+1))).mp (min_le_right c₀ (1/(8*(B+1))))
    dsimp[c]
    nlinarith
  have hBc:0 ≤ B*c:=mul_nonneg hB.le hc.le
  have hc8:8*c ≤ 1:=by nlinarith
  have hBc8:8*B*c ≤ 1:=by nlinarith
  have hprod:=mul_le_mul_of_nonneg_right hc8 (mul_nonneg (by norm_num:(0:ℝ) ≤ 8) hBc)
  have hbase:16*B*c^2 ≤ 1:=by nlinarith
  let H:ℝ:=max 1 ((c⁻¹)^2)
  have hH:0<H:=by dsimp[H];exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨c,H,hc,min_le_left _ _,hH,?_⟩
  intro h hhH K hK
  have hh:0<h:=hH.trans_le hhH
  have hs:0 ≤ Real.sqrt h:=Real.sqrt_nonneg _
  have hs2:(Real.sqrt h)^2=h:=Real.sq_sqrt hh.le
  have hhInv:(c⁻¹)^2 ≤ h:=(le_max_right _ _).trans hhH
  have hlarge:=mul_le_mul_of_nonneg_left hhInv (sq_nonneg c)
  have heInv:c^2*(c⁻¹)^2=1:=by field_simp[hc.ne']
  rw[heInv] at hlarge
  have ht0:0 ≤ c*Real.sqrt h:=mul_nonneg hc.le hs
  have ht1:1 ≤ c*Real.sqrt h:=by nlinarith
  have hK1:(K:ℝ)+1 ≤ 2*c*Real.sqrt h:=by linarith
  have hK2:=pow_le_pow_left₀ (by positivity:(0:ℝ) ≤ (K:ℝ)+1) hK1 2
  have hb:=mul_le_mul_of_nonneg_right hbase hh.le
  have hleft:=mul_le_mul_of_nonneg_left hK2 (show 0 ≤ 4*B by positivity)
  nlinarith
end WP.Analysis
