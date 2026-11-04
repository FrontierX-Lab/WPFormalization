import WPFormalization.Coefficients.AdjacentChiPrediction
import WPFormalization.Coefficients.AdjacentBulkPowerRates
/-! Both actual bulk adjacent-ratio rates for the original coefficient error.
The trigonometric prediction retains every finite-h shift, including m=1.
Only P and the explicitly positive density parameter remain as premises. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology
lemma adjacentError_power_rate_of_log_rate (P:PsiTheory) (s b e:ℝ)
    (hs:0<s)(he:e<0)(hbe:-b ≤ e)
    (hlog:∃C:ℝ,0<C ∧∃G:ℕ,∀g≥G,∀k:ℕ,s*Real.rpow (g:ℝ) b ≤ k→k<3*g-2→
      |adjacentLogRatio P g k-Real.log (adjacentProfileQ ((k:ℝ)/g))| ≤ C*Real.rpow (g:ℝ) e) :
    ∃C:ℝ,0<C ∧∃G:ℕ,∀g≥G,∀k:ℕ,s*Real.rpow (g:ℝ) b ≤ k→k<3*g-2→
      adjacentError P g k ≤ C*Real.rpow (g:ℝ) e := by
  obtain ⟨C,hC,G,hlog⟩:=hlog
  obtain ⟨D,hD,hprediction⟩:=adjacentSaddlePrediction_log_calibration
  let E:ℝ:=C+D/s
  have hE:0<E:=by dsimp[E];positivity
  have ht:Tendsto (fun g:ℕ=>Real.rpow (g:ℝ) e) atTop (𝓝 (0:ℝ)) := by
    simpa only[Function.comp_def,Real.rpow_eq_pow,neg_neg] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr he)).comp tendsto_natCast_atTop_atTop
  have htE:Tendsto (fun g:ℕ=>E*Real.rpow (g:ℝ) e) atTop (𝓝 (0:ℝ)) := by
    simpa only[mul_zero] using tendsto_const_nhds.mul ht
  obtain ⟨G0,hG0⟩:=eventually_atTop.mp (htE.eventually (eventually_lt_nhds (by norm_num:(0:ℝ)<1)))
  refine ⟨2*E,by positivity,max G (max G0 1),?_⟩
  intro g hg k hk hkN
  have hgG:G ≤ g:=(le_max_left _ _).trans hg
  have hgG0:G0 ≤ g:=(le_max_left G0 1).trans ((le_max_right G (max G0 1)).trans hg)
  have hg1:1 ≤ g:=(le_max_right G0 1).trans ((le_max_right G (max G0 1)).trans hg)
  have hgr:(0:ℝ)<g:=by exact_mod_cast (show 0<g by omega)
  have hgr1:(1:ℝ) ≤ g:=by exact_mod_cast hg1
  have hkr:(0:ℝ)<k:=(mul_pos hs (Real.rpow_pos_of_pos hgr b)).trans_le hk
  have hkNat:0<k:=by exact_mod_cast hkr
  have hk1:1 ≤ k:=by omega
  have hinv:1/(k:ℝ) ≤ (1/s)*Real.rpow (g:ℝ) e := by
    have hneg:Real.rpow (g:ℝ) (-b)=(Real.rpow (g:ℝ) b)⁻¹:=Real.rpow_neg hgr.le b
    calc _  ≤  1/(s*Real.rpow (g:ℝ) b) := one_div_le_one_div_of_le (mul_pos hs (Real.rpow_pos_of_pos hgr b)) hk
         _ = (1/s)*Real.rpow (g:ℝ) (-b) := by rw[hneg];ring
         _  ≤  _ := mul_le_mul_of_nonneg_left
           (show Real.rpow (g:ℝ) (-b) ≤ Real.rpow (g:ℝ) e from Real.rpow_le_rpow_of_exponent_le hgr1 hbe)
           (by positivity)
  have herr:|adjacentLogRatio P g k-Real.log (adjacentSaddlePrediction g k/(g:ℝ)^2)| ≤ E*Real.rpow (g:ℝ) e := by
    calc _  ≤  |adjacentLogRatio P g k-Real.log (adjacentProfileQ ((k:ℝ)/g))|+
          |Real.log (adjacentProfileQ ((k:ℝ)/g))-Real.log (adjacentSaddlePrediction g k/(g:ℝ)^2)| := abs_sub_le _ _ _
         _  ≤  C*Real.rpow (g:ℝ) e+D/(k:ℝ) := by
           apply add_le_add (hlog g hgG k hk hkN)
           rw[abs_sub_comm]
           exact hprediction g k hg1 hk1 hkN
         _  ≤  E*Real.rpow (g:ℝ) e := by
           have hi:=mul_le_mul_of_nonneg_left hinv hD.le
           calc _ = C*Real.rpow (g:ℝ) e+D*(1/(k:ℝ)) := by ring
                _  ≤  C*Real.rpow (g:ℝ) e+D*((1/s)*Real.rpow (g:ℝ) e) := add_le_add le_rfl hi
                _ = _ := by dsimp[E];ring
  rw[adjacentError_eq_exp_log_prediction P g k hg1 hkN]
  calc _  ≤  2*|adjacentLogRatio P g k-Real.log (adjacentSaddlePrediction g k/(g:ℝ)^2)| :=
         Real.abs_exp_sub_one_le (herr.trans (hG0 g hgG0).le)
       _  ≤  2*(E*Real.rpow (g:ℝ) e) := mul_le_mul_of_nonneg_left herr (by norm_num)
       _ = _ := by ring

lemma adjacentError_three_quarter_bulk_rate (P:PsiTheory) :
    ∃C:ℝ,0<C ∧∃G:ℕ,∀g≥G,∀k:ℕ,Real.rpow (g:ℝ) (3/4:ℝ) ≤ k→k<3*g-2→
      adjacentError P g k ≤ C*Real.rpow (g:ℝ) (-1/8:ℝ) := by
  simpa only[one_mul] using adjacentError_power_rate_of_log_rate P 1 (3/4) (-1/8)
    (by norm_num) (by norm_num) (by norm_num) (by simpa only[one_mul] using adjacentLogRatio_three_quarter_rate P)

lemma adjacentError_positive_density_rate (P:PsiTheory) (ε:ℝ)(hε:0<ε) :
    ∃C:ℝ,0<C ∧∃G:ℕ,∀g≥G,∀k:ℕ,ε*(g:ℝ) ≤ k→k<3*g-2→
      adjacentError P g k ≤ C*Real.rpow (g:ℝ) (-1/4:ℝ) := by
  simpa only[Real.rpow_eq_pow,Real.rpow_one] using adjacentError_power_rate_of_log_rate P ε 1 (-1/4)
    hε (by norm_num) (by norm_num) (by simpa only[Real.rpow_eq_pow,Real.rpow_one] using adjacentLogRatio_positive_density_rate P ε hε)

end WP.Coefficients
