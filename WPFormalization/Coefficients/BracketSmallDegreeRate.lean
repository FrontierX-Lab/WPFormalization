import WPFormalization.Coefficients.BracketGapLogBound
import WPFormalization.Coefficients.BracketShortWindow
import WPFormalization.Analysis.SmallDegreeAlgebra
/-! Genuine uniform g^(-1/8) bracket ratio control for every k<=g^(3/4), supplied by C.8 and the original C.7/C.23 finite block argument. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Filter
open scoped Topology
lemma bracketAdjacentRatio_small_degree_rate (P:PsiTheory):
    ∃C:ℝ,0 < C∧∃G:ℕ,∀g:ℕ,G ≤ g →∀k:ℕ,(k:ℝ) ≤ (g:ℝ)^(3/4:ℝ) →
      0 ≤ bracketAdjacentRatio P g k-1∧
      bracketAdjacentRatio P g k-1 ≤ C*(g:ℝ)^(-1/8:ℝ):=by
  obtain ⟨A,hA,hshort⟩:=bracketAdjacentRatio_short_window P
  obtain ⟨D,hD,G,hgap⟩:=bracketAdjacentRatio_truncated_gap_log_bound P
  obtain ⟨E,T,hE,hT,halg⟩:=Analysis.small_degree_truncated_gap_rate A D hA hD
  have hlarge:Tendsto (fun g:ℕ=>(g:ℝ)^(1/8:ℝ)) atTop atTop:=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop
  obtain ⟨G1,hG1⟩:=eventually_atTop.mp (hlarge.eventually_ge_atTop T)
  refine ⟨E,hE,max (max G G1) 4,?_⟩
  intro g hg k hk
  have hgG:G ≤ g:=(le_max_left _ _).trans ((le_max_left _ _).trans hg)
  have hgG1:G1 ≤ g:=(le_max_right _ _).trans ((le_max_left _ _).trans hg)
  have hg4:4 ≤ g:=(le_max_right _ _).trans hg
  have hg1:1 ≤ g:=by omega
  have hgR:(4:ℝ) ≤ g:=by exact_mod_cast hg4
  have hg0:0 < (g:ℝ):=by linarith only[hgR]
  let t:ℝ:=(g:ℝ)^(1/8:ℝ)
  have ht:T ≤ t:=hG1 g hgG1
  have ht1:1 ≤ t:=hT.trans ht
  have ht0:0 < t:=zero_lt_one.trans_le ht1
  have ht8:t^8=(g:ℝ):=by
    dsimp[t]
    rw[←Real.rpow_mul_natCast hg0.le]
    norm_num
  have ht6:t^6=(g:ℝ)^(3/4:ℝ):=by
    dsimp[t]
    rw[←Real.rpow_mul_natCast hg0.le]
    norm_num
  have ht68:t^6 ≤ t^8:=pow_le_pow_right₀ ht1 (by norm_num)
  have hkg:(k:ℝ) ≤ g:=by rw[ht6,ht8] at ht68;exact hk.trans ht68
  have hkn:k ≤ g:=by exact_mod_cast hkg
  have hvalid:2*(k+1) ≤ 3*g-2:=by omega
  have hkN:k < 3*g-2:=by omega
  have hη:0 ≤ bracketAdjacentRatio P g k-1:=sub_nonneg.mpr (bracketAdjacentRatio_ge_one P g k hg1 hkN)
  refine ⟨hη,?_⟩
  have hlog:Real.log ((g:ℝ)+1) ≤ 16*t:=by
    have hl:Real.log ((g:ℝ)+1) ≤ Real.log 2+Real.log (g:ℝ):=by
      rw[←Real.log_mul (by norm_num:(2:ℝ)≠0) hg0.ne']
      exact Real.log_le_log (by positivity) (by linarith only[hgR])
    have h2:Real.log 2 ≤ Real.log (g:ℝ):=Real.log_le_log (by norm_num) (by linarith only[hgR])
    have hp:=Real.log_le_rpow_div hg0.le (by norm_num:(0:ℝ) < 1/8)
    change Real.log (g:ℝ) ≤ t/(1/8:ℝ) at hp
    nlinarith only[hl,h2,hp]
  have hb:=halg (g:ℝ) ((k:ℝ)+1) (Real.log ((g:ℝ)+1)) t (bracketAdjacentRatio P g k-1)
    ht (by positivity) (by rw[ht6];linarith only[hk]) ht8.symm
    (Real.log_nonneg (by linarith only[hgR])) hlog hη
    (fun hw=>by simpa only[div_eq_mul_inv,mul_assoc] using (hshort g hg1 k hkN hw).2)
    (by simpa only[div_eq_mul_inv,mul_assoc] using hgap g hgG hg1 k hvalid)
  have hinv:(g:ℝ)^(-1/8:ℝ)=t⁻¹:=by
    dsimp[t]
    rw[←Real.rpow_neg hg0.le]
    norm_num
  rw[hinv]
  simpa only[div_eq_mul_inv] using hb
end WP.Coefficients
