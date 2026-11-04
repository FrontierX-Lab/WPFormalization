import WPFormalization.Analysis.SaddleActionIncrement
import WPFormalization.Coefficients.SaddleActionRegularity
/-! The actual unscaled-kernel saddle action changes by O(log(h+1)) under (h,m) to (h+1,m+2), including m=0. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Set

lemma unscaledLogPotential_zero : unscaledLogPotential 0=0:=by
  simp[unscaledLogPotential,H_zero,Analysis.derivX_zero]

lemma unscaled_saddle_uniform_increment_bounds:
    ∃ K:ℝ,0 < K∧1 ≤ K∧
      (∀z∈Icc (0:ℝ) (r 0),unscaledMean z ≤ K*z)∧
      ∀x∈Icc (0:ℝ) (r 0),∀y∈Icc (0:ℝ) (r 0),x ≤ y →
        0 ≤ unscaledLogPotential y-unscaledLogPotential x∧
          unscaledLogPotential y-unscaledLogPotential x ≤ K*(y-x):=by
  obtain ⟨C,hC,hb⟩:=unscaledMean_uniform_linear_variance_bounds
  obtain ⟨D,hD,hd⟩:=unscaled_log_potential_bounds
  let K:ℝ:=max 1 (max C D)
  have hK:1 ≤ K:=le_max_left _ _
  have hCK:C ≤ K:=(le_max_left _ _).trans (le_max_right _ _)
  have hDK:D ≤ K:=(le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K,lt_of_lt_of_le zero_lt_one hK,hK,?_,?_⟩
  · intro z hz
    exact (hb z hz).2.1.trans (mul_le_mul_of_nonneg_right hCK hz.1)
  · intro x hx y hy hxy
    have H:=Analysis.real_log_action_ordered_difference unscaledLogPotential (r 0) K
      (fun z hz=>(unscaledLogPotential_hasDerivAt z hz).differentiableAt)
      (fun z hz=>⟨(hd z hz).1,(hd z hz).2.trans hDK⟩) x y hx hy hxy
    exact H

def unscaledSaddleAction (h m:ℝ):ℝ:=
  h*unscaledLogPotential (saddleZeta (m/h))-m*Real.log (saddleZeta (m/h))

lemma unscaledSaddleAction_shift_bound:
    ∃C:ℝ,0 < C∧∀h:ℕ,1 ≤ h →∀m:ℕ,2*m+1 ≤ 3*h →
      |unscaledSaddleAction ((h:ℝ)+1) ((m:ℝ)+2)-unscaledSaddleAction h m| ≤
        C*Real.log ((h:ℝ)+1):=by
  obtain ⟨K,hK,hK1,hmean,hinc⟩:=unscaled_saddle_uniform_increment_bounds
  let R:ℝ:=r 0
  have hR:0 < R:=r_pos 0 ⟨le_rfl,y₀_pos⟩
  let D:ℝ:=|Real.log 2|+|Real.log K|+|Real.log R|+1
  let C:ℝ:=2*(20*K+K*R+2*D)+2
  have hC:0 < C:=by dsimp[C,D];positivity
  refine ⟨C,hC,?_⟩
  intro h hh m hm
  let H:ℝ:=h
  let M:ℝ:=m
  have hH:1 ≤ H:=by dsimp[H];exact_mod_cast hh
  have hH0:0 < H:=zero_lt_one.trans_le hH
  have hHp:0 < H+1:=by linarith only[hH]
  have hM:0 ≤ M:=Nat.cast_nonneg m
  have hmR:2*M+1 ≤ 3*H:=by dsimp[M,H];exact_mod_cast hm
  let u:ℝ:=M/H
  let v:ℝ:=(M+2)/(H+1)
  have hu:u∈Icc (0:ℝ) (3/2):=by
    refine ⟨div_nonneg hM hH0.le,?_⟩
    apply (div_le_iff₀ hH0).mpr
    nlinarith only[hmR]
  have hv:v∈Icc (0:ℝ) (3/2):=by
    refine ⟨div_nonneg (by positivity) hHp.le,?_⟩
    apply (div_le_iff₀ hHp).mpr
    nlinarith only[hmR]
  have huv:u ≤ v:=by
    apply (div_le_div_iff₀ hH0 hHp).mpr
    nlinarith only[hmR,hH,hM]
  have hdiff:v-u ≤ 2/H:=by
    have ht:(M+2)/(H+1) ≤ (M+2)/H:=
      div_le_div_of_nonneg_left (by positivity) hH0 (by linarith)
    dsimp[u,v]
    have he:(M+2)/H-M/H=2/H:=by ring
    linarith only[ht,he]
  let z:ℝ:=saddleZeta u
  let w:ℝ:=saddleZeta v
  have hzs:=saddleZeta_spec u hu
  have hws:=saddleZeta_spec v hv
  have hdz:=saddleZeta_ordered_lipschitz u v hu hv huv
  change 0 ≤ w-z∧w-z ≤ 5*(v-u) at hdz
  have hdz0:0 ≤ w-z:=hdz.1
  have hdzU:H*(w-z) ≤ 10:=by
    have ht:w-z ≤ 10/H:=by
      calc
        _ ≤ 5*(v-u):=hdz.2
        _ ≤ 5*(2/H):=mul_le_mul_of_nonneg_left hdiff (by norm_num)
        _ = _:=by ring
    have ht':=(le_div_iff₀ hH0).mp ht
    nlinarith only[ht']
  have hMz:M ≤ K*H*z:=by
    have ht:=hmean z hzs.1
    rw[hzs.2] at ht
    have ht':=(div_le_iff₀ hH0).mp ht
    nlinarith only[ht']
  have hwlower:2 ≤ K*(H+1)*w:=by
    have ht:=hmean w hws.1
    rw[hws.2] at ht
    have ht':=(div_le_iff₀ hHp).mp ht
    nlinarith only[ht',hM]
  have hAB:=hinc z hzs.1 w hws.1 (by linarith only[hdz0])
  have hB:=hinc 0 ⟨le_rfl,hR.le⟩ w hws.1 hws.1.1
  rw[unscaledLogPotential_zero,sub_zero,sub_zero] at hB
  have hBR:unscaledLogPotential w ≤ K*R:=
    hB.2.trans (mul_le_mul_of_nonneg_left hws.1.2 hK.le)
  have hb:=Analysis.log_saddle_action_increment_bound H M z w
    (unscaledLogPotential z) (unscaledLogPotential w) K R hH hM hK hR hzs.1.1
    hdz0 hdzU hMz hwlower hws.1.2 hAB.1 hAB.2 hB.1 hBR
  change _ ≤ C*Real.log (H+1)
  exact hb
end WP.Coefficients
