import WPFormalization.HigherOrder.ProfileTopologyForcing
import WPFormalization.HigherOrder.OrderWeights
import WPFormalization.HigherOrder.ProfileLowCore
import WPFormalization.Analysis.FactorialKernelMoments
/-! The central separating source is genuinely summable. The original
C.5 growing-loss bound propagates through the full degree kernel, yielding
a uniform S_L^(2L-1) forcing term. A fixed small-weight threshold ensures
the original topology bound's minimum parent complexity; no order-dependent
threshold or pre-assumed source remainder is introduced. -/
noncomputable section
namespace WP.HigherOrder
open Set

def recursiveSeparatingWeightedCentral (P:PsiTheory)(g t L:ℕ)(d:List ℕ)(Y:ℝ):ℝ :=
  ∑'l:ℕ,weight Y l*(recursiveSeparatingTail P g (t+l) L d Y/2)

lemma recursiveSeparatingWeightedCentral_summable (P:PsiTheory)(g t L:ℕ)(d:List ℕ)
    (hg:2 ≤ g)(Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀) :
    Summable (fun l:ℕ=>weight Y l*(recursiveSeparatingTail P g (t+l) L d Y/2)) := by
  obtain ⟨C,B,hC,hB,hw⟩:=Analysis.weight_factorial_moments
  have hws:Summable (fun l:ℕ=>((l:ℝ)+1)*|weight Y l|):=by simpa only[pow_one] using (hw 1 Y hY).1
  let Z:=markedSplitLossTail P g (d.length+1) 1 L Y
  have hZ:0 ≤ Z:=recursiveSeparating_zero_mass_nonneg P g d.length L hg Y hY
  have hnonneg(l:ℕ):0 ≤ weight Y l*(recursiveSeparatingTail P g (t+l) L d Y/2):=
    mul_nonneg (weight_nonneg Y hY l) (div_nonneg (recursiveSeparatingTail_nonneg P g (t+l) L d hg Y hY) (by norm_num))
  apply Summable.of_nonneg_of_le hnonneg _ (hws.mul_left (Z*((t:ℝ)+1)))
  intro l
  have hn:(((t+l-1:ℕ):ℝ)) ≤ ((t:ℝ)+1)*((l:ℝ)+1):=by
    have ht:(((t+l-1:ℕ):ℝ)) ≤ (t:ℝ)+l:=by exact_mod_cast (show t+l-1 ≤ t+l by omega)
    nlinarith[Nat.cast_nonneg (α:=ℝ) t,Nat.cast_nonneg (α:=ℝ) l]
  have hb:=recursiveSeparatingTail_le_zero P g (t+l) L d hg Y hY
  have hpos:=recursiveSeparatingTail_nonneg P g (t+l) L d hg Y hY
  have htail:recursiveSeparatingTail P g (t+l) L d Y/2 ≤ ((t:ℝ)+1)*((l:ℝ)+1)*Z:=by
    have hb':recursiveSeparatingTail P g (t+l) L d Y ≤ (((t+l-1:ℕ):ℝ))*Z:=hb
    have hh:=mul_le_mul_of_nonneg_right hn hZ
    linarith
  have hmul:=mul_le_mul_of_nonneg_left htail (weight_nonneg Y hY l)
  rw[abs_of_nonneg (weight_nonneg Y hY l)]
  convert hmul using 1 <;>ring

lemma recursiveSeparatingWeightedCentral_prefix_limit :
    ∃C:ℝ,0<C ∧∀P:PsiTheory,∀g t L:ℕ,∀d:List ℕ,2 ≤ g→∀Y∈Icc (0:ℝ) y₀,
      |recursiveSeparatingWeightedCentral P g t L d Y| ≤
        C*((t:ℝ)+1)*markedSplitLossTail P g (d.length+1) 1 L Y := by
  obtain ⟨C,hC,hprefix⟩:=recursiveSeparating_tail_kernel_prefix
  refine ⟨C,hC,?_⟩
  intro P g t L d hg Y hY
  have hs:=recursiveSeparatingWeightedCentral_summable P g t L d hg Y hY
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat.abs (Filter.Eventually.of_forall (fun N=>hprefix P g t L d hg N Y hY))

lemma separating_central_small_weight_uniform (P:PsiTheory) :
    ∃C B δ₀:ℝ,0<C ∧ 0<B ∧ 0<δ₀ ∧ δ₀ ≤ 1 ∧∀M:ℝ,2 ≤ M→
    ∀g t L:ℕ,∀d:List ℕ,Stable g (d.length+1)→2 ≤ L→
    profileOrderWeight M L (t::d)^2/(complexity g (d.length+1):ℝ)<δ₀→
    ∀Y∈Icc (0:ℝ) y₀,
      |recursiveSeparatingWeightedCentral P g t L d Y| ≤
        C*B^L*profileOrderWeight M L (t::d)^(2*L-1)/(complexity g (d.length+1):ℝ)^L := by
  obtain ⟨C₁,hC₁,hprefix⟩:=recursiveSeparatingWeightedCentral_prefix_limit
  obtain ⟨C,B,hC,hB,H,hS,hT⟩:=topology_tails P 4 (by norm_num)
  let δ₀:ℝ:=1/((H:ℝ)+1)
  have hδ:0<δ₀:=by dsimp[δ₀];positivity
  have hδ1:δ₀ ≤ 1:=by
    dsimp[δ₀]
    apply (div_le_one (by positivity:(0:ℝ)<(H:ℝ)+1)).mpr
    linarith[Nat.cast_nonneg (α:=ℝ) H]
  refine ⟨C₁*C,B,δ₀,by positivity,hB,hδ,hδ1,?_⟩
  intro M hM g t L d hs hL hsmall Y hY
  let p:=d.length+1
  let S:=profileOrderWeight M L (t::d)
  let h:ℝ:=complexity g p
  have hh:0<h:=by
    dsimp[h,p]
    have hn:0<complexity g (d.length+1):=by unfold complexity Stable at *;omega
    exact_mod_cast hn
  have hp:1 ≤ p:=by dsimp[p];omega
  have hpR:(1:ℝ) ≤ p:=by exact_mod_cast hp
  have hLR:(2:ℝ) ≤ L:=by exact_mod_cast hL
  have hMmul:=mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg L : (0:ℝ) ≤ L)
  have hSbound:(p:ℝ)+2*L ≤ S:=by
    dsimp[S,p,profileOrderWeight]
    simp only[List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith[Nat.cast_nonneg (α:=ℝ) (t::d).sum]
  have hS1:1 ≤ S:=by linarith
  have hS0:0 ≤ S:=by linarith
  have hsmall1:S^2/h<1:=hsmall.trans_le hδ1
  have hSsq:S^2<h:=(div_lt_one hh).mp hsmall1
  have hgLarge:=small_weight_parent_genus_large g p L S hp (by omega) hs hSbound hsmall1
  have hg:2 ≤ g:=by omega
  have hlargeR:(H:ℝ) ≤ h:=by
    have hprod:S^2*((H:ℝ)+1)<h:=by
      simpa only[one_mul] using (div_lt_div_iff₀ hh (by positivity:(0:ℝ)<(H:ℝ)+1)).mp hsmall
    have hSsq1:1 ≤ S^2:=by nlinarith
    nlinarith[Nat.cast_nonneg (α:=ℝ) H]
  have hlarge:H ≤ complexity g p:=by dsimp[h] at hlargeR;exact_mod_cast hlargeR
  have hproot:(p:ℝ) ≤ Real.sqrt h:=by
    apply (Real.le_sqrt (Nat.cast_nonneg p) hh.le).mpr
    exact (pow_le_pow_left₀ (Nat.cast_nonneg p) (by linarith:p ≤ S) 2).trans hSsq.le
  have hLroot:(L:ℝ) ≤ Real.sqrt h:=by
    apply (Real.le_sqrt (Nat.cast_nonneg L) hh.le).mpr
    exact (pow_le_pow_left₀ (Nat.cast_nonneg L) (by linarith:L ≤ S) 2).trans hSsq.le
  have htail:=hS g p hp hlarge (hproot.trans (by nlinarith[Real.sqrt_nonneg h])) L hL hLroot Y hY
  have hpref:=hprefix P g t L d hg Y hY
  change |recursiveSeparatingWeightedCentral P g t L d Y| ≤ C₁*((t:ℝ)+1)*markedSplitLossTail P g p 1 L Y at hpref
  have hmass:=mul_le_mul_of_nonneg_left htail (by positivity:0 ≤ C₁*((t:ℝ)+1))
  apply hpref.trans (hmass.trans _)
  have ht:(t:ℝ)+1 ≤ S:=by
    have hsum:t ≤ (t::d).sum:=by simp only[List.sum_cons];omega
    have hsumR:(t:ℝ) ≤ ((t::d).sum:ℝ):=by exact_mod_cast hsum
    dsimp[S,profileOrderWeight]
    simp only[List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith[Nat.cast_nonneg (α:=ℝ) d.length,Nat.cast_nonneg (α:=ℝ) L]
  have hpL:(p:ℝ)+L ≤ S:=by linarith
  have hPow1:((t:ℝ)+1)*((p:ℝ)+L)^L ≤ S^(L+1):=by
    exact (mul_le_mul ht (pow_le_pow_left₀ (by positivity) hpL L) (by positivity) hS0).trans_eq (by rw[pow_succ];ring)
  have hPow2:S^(L+1) ≤ S^(2*L-1):=pow_le_pow_right₀ hS1 (by omega)
  have hbound:=mul_le_mul_of_nonneg_left (hPow1.trans hPow2)
    (by positivity:0 ≤ C₁*C*B^L/h^L)
  convert hbound using 1 <;> (try simp only[div_pow,mul_pow]) <;> (try dsimp[S,h,p]) <;>ring

end WP.HigherOrder
