import WPFormalization.Analysis.SaddleInverseSupport
/-! A logarithmic endpoint-uniform bound for a bounded increment of both saddle parameters. -/
set_option autoImplicit false
noncomputable section
namespace WP.Analysis
open Set

lemma log_saddle_action_increment_bound (H M z w A B K R:ℝ)
    (hH:1 ≤ H)(hM:0 ≤ M)(hK:0 < K)(hR:0 < R)(hz:0 ≤ z)
    (hzw:0 ≤ w-z)(hd:H*(w-z) ≤ 10)(hMz:M ≤ K*H*z)
    (hw:2 ≤ K*(H+1)*w)(hwR:w ≤ R)
    (hAB:0 ≤ B-A)(hABU:B-A ≤ K*(w-z))(hB:0 ≤ B)(hBU:B ≤ K*R):
    let D:=|Real.log 2|+|Real.log K|+|Real.log R|+1
    |((H+1)*B-(M+2)*Real.log w)-(H*A-M*Real.log z)| ≤
      (2*(20*K+K*R+2*D)+2)*Real.log (H+1):=by
  let D:=|Real.log 2|+|Real.log K|+|Real.log R|+1
  have hH0:0 < H:=zero_lt_one.trans_le hH
  have hHp:0 < H+1:=by linarith only[hH]
  have hKHp:0 < K*(H+1):=mul_pos hK hHp
  have hw0:0 < w:=by nlinarith only[hw,hKHp]
  have hlow:2/(K*(H+1)) ≤ w:=(div_le_iff₀ hKHp).mpr (by nlinarith only[hw])
  have hl:=Real.log_le_log (div_pos (by norm_num) hKHp) hlow
  rw[Real.log_div (by norm_num:(2:ℝ)≠0) hKHp.ne',Real.log_mul hK.ne' hHp.ne'] at hl
  have hu:=Real.log_le_log hw0 hwR
  have hlog2:1/2 ≤ Real.log (H+1):=by
    have ht:=Real.log_le_log (by norm_num:(0:ℝ) < 2) (show 2 ≤ H+1 by linarith only[hH])
    linarith only[ht,Real.log_two_gt_d9]
  have hD:0 < D:=by dsimp[D];positivity
  have hlog:|Real.log w| ≤ Real.log (H+1)+D:=by
    apply abs_le.mpr
    dsimp[D]
    constructor
    · linarith only[hl,neg_abs_le (Real.log 2),le_abs_self (Real.log K),abs_nonneg (Real.log R)]
    · linarith only[hu,le_abs_self (Real.log R),abs_nonneg (Real.log 2),abs_nonneg (Real.log K),hlog2]
  have hweight:|M*(Real.log w-Real.log z)| ≤ 10*K:=by
    by_cases hM0:M=0
    · rw[hM0,zero_mul,abs_zero]
      positivity
    · have hMp:0 < M:=lt_of_le_of_ne hM (Ne.symm hM0)
      have hzp:0 < z:=by
        by_contra hn
        have he:z=0:=le_antisymm (le_of_not_gt hn) hz
        rw[he,mul_zero] at hMz
        linarith only[hMp,hMz]
      have hlogdiff:=log_ordered_difference_le z w hzp (by linarith only[hzw])
      have hld:z*(Real.log w-Real.log z) ≤ w-z:=by
        have ht:=(le_div_iff₀ hzp).mp hlogdiff.2
        nlinarith only[ht]
      have hleft:z*(M*(Real.log w-Real.log z)) ≤ M*(w-z):=by
        convert mul_le_mul_of_nonneg_left hld hM using 1 <;>ring
      have hright:M*(w-z) ≤ z*(10*K):=by
        calc
          _ ≤ (K*H*z)*(w-z):=mul_le_mul_of_nonneg_right hMz hzw
          _ = (K*z)*(H*(w-z)):=by ring
          _ ≤ (K*z)*10:=mul_le_mul_of_nonneg_left hd (mul_nonneg hK.le hz)
          _ = _:=by ring
      rw[abs_of_nonneg (mul_nonneg hM hlogdiff.1)]
      nlinarith only[hleft.trans hright,hzp]
  have hA0:0 ≤ H*(B-A)+B:=add_nonneg (mul_nonneg hH0.le hAB) hB
  have hAup:H*(B-A)+B ≤ 10*K+K*R:=by
    calc
      _ ≤ H*(K*(w-z))+K*R:=add_le_add (mul_le_mul_of_nonneg_left hABU hH0.le) hBU
      _ = K*(H*(w-z))+K*R:=by ring
      _ ≤ _:=by
        have ht:=mul_le_mul_of_nonneg_left hd hK.le
        nlinarith only[ht]
  have he:((H+1)*B-(M+2)*Real.log w)-(H*A-M*Real.log z)=
      (H*(B-A)+B)-M*(Real.log w-Real.log z)-2*Real.log w:=by ring
  rw[he]
  have habs:=abs_sub (H*(B-A)+B-M*(Real.log w-Real.log z)) (2*Real.log w)
  have habs':=abs_sub (H*(B-A)+B) (M*(Real.log w-Real.log z))
  rw[abs_of_nonneg hA0] at habs'
  rw[abs_mul,abs_of_pos (by norm_num:(0:ℝ) < 2)] at habs
  change _ ≤ (2*(20*K+K*R+2*D)+2)*Real.log (H+1)
  have hbase:0 ≤ 20*K+K*R+2*D:=by positivity
  have hscale:=mul_le_mul_of_nonneg_left hlog2 hbase
  nlinarith only[habs,habs',hAup,hweight,hlog,hscale]
end WP.Analysis
