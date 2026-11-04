import WPFormalization.HigherOrder.LinearRemainderStage
import WPFormalization.HigherOrder.SeparatingCompleteRemainderStep
/-! The genuine merger, handle and low-plus-central separating source
remainders share a single positive strict-loss convolution and the sharp
edge scale S_L^(2L-1). All original coefficients, kernels, source pairings
and topology forcing are instantiated; only previous stage bounds enter. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma recursive_operator_remainder_stage (P:PsiTheory) :
    ∃D B δ₀:ℝ,∃M₀:ℕ,0<D ∧ 1 ≤ B ∧ 0<δ₀ ∧ δ₀ ≤ 1 ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀L:ℕ,2 ≤ L→∀e:ℕ→ℝ,(∀q,0 ≤ e q)→
    (∀q:ℕ,1 ≤ q→q<L→∀s,RemainderStageBound P M s q (e q))→
    ∀g k:ℕ,2 ≤ g→∀d:List ℕ,∀Y∈Icc (0:ℝ) y₀,
    profileOrderWeight (M:ℝ) L (k::d)^2/(complexity g (d.length+1):ℝ)<δ₀→
    |recursiveMerger P g k d Y+recursiveHandle P g k d Y+
      (recursiveSeparatingWeightedLow P g k L d Y+recursiveSeparatingWeightedCentral P g k L d Y)-
      truncationValue (mergerSeries Y (formalHierarchyJet P Y) k d+
        nonseparatingSeries Y (formalHierarchyJet P Y) k d+
        separatingSeries P Y (formalHierarchyJet P Y) (L-1) k d) L (1/(complexity g (d.length+1):ℝ))| ≤
      D*profileOrderWeight (M:ℝ) L (k::d)^(2*L-1)/(complexity g (d.length+1):ℝ)^L*
        ((∑i∈Finset.Icc 1 L,B^i*e (L-i))+B^L):=by
  classical
  obtain ⟨Dl,Bl,Ml,hDl,hBl,hMl,hlinear⟩:=recursive_linear_remainder_stage P
  obtain ⟨Cs,Bs,δ₀,Ms,hCs,hBs,hδ₀,hδ1,hMs,hsep⟩:=recursiveSeparating_uniform_remainder_step P
  let B:=max Bl Bs
  have hB:1 ≤ B:=hBl.trans (le_max_left _ _)
  let D:=Dl+3*Cs
  refine ⟨D,B,δ₀,max Ml Ms,by dsimp[D];positivity,hB,hδ₀,hδ1,hMl.trans (le_max_left _ _),?_⟩
  intro M hM L hL e he hprev g k hg d Y hY hsmall
  let S:=profileOrderWeight (M:ℝ) L (k::d)
  let h:ℝ:=complexity g (d.length+1)
  let V:=∑i∈Finset.Icc 1 L,B^i*e (L-i)
  have hS:0 ≤ S:=by dsimp[S,profileOrderWeight];positivity
  have hh:0<h:=by dsimp[h];exact_mod_cast (show 0<complexity g (d.length+1) by unfold complexity;omega)
  have hV:0 ≤ V:=Finset.sum_nonneg (fun i hi=>mul_nonneg (pow_nonneg (show 0 ≤ B by linarith) _) (he _))
  have hcusp (g' p' q:ℕ) (hp':1 ≤ p') (hs':Stable g' p') (hq:1 ≤ q) (hqL:q<L):
      |cuspCorrection P g' p' Y-truncationValue (formalCusp P Y p') q (1/(complexity g' p':ℝ))| ≤
        e q*scalarOrderWeight (M:ℝ) q p'^(2*q)/(complexity g' p':ℝ)^q:=by
    exact hprev q hq hqL 1 g' p' trivial hp' hs' (by unfold Stable complexity at *;omega) Y hY
  have hgenus (g' p' q:ℕ) (hp':1 ≤ p') (hs':Stable g' p') (hq:1 ≤ q) (hqL:q<L):
      |genusCorrection P g' p' Y-truncationValue (formalGenus P Y p') q (1/(complexity g' p':ℝ))| ≤
        e q*scalarOrderWeight (M:ℝ) q p'^(2*q)/(complexity g' p':ℝ)^q:=by
    by_cases hp1:p'=1
    · exact hprev q hq hqL 3 g' p' hp1 hp' hs' (by unfold Stable complexity at *;omega) Y hY
    · exact hprev q hq hqL 2 g' p' (by omega) hp' hs' (by unfold Stable complexity at *;omega) Y hY
  have hprof (g':ℕ) (v:List ℕ) (hv:1 ≤ v.length) (hs':Stable g' v.length) (q:ℕ) (hq:1 ≤ q) (hqL:q<L):
      |profile P g' v Y-truncationValue (formalProfile P Y v) q (1/(complexity g' v.length:ℝ))| ≤
        e q*profileOrderWeight (M:ℝ) q v^(2*q)/(complexity g' v.length:ℝ)^q:=by
    exact hprev q hq hqL 0 g' v hv hs' (by unfold Stable complexity at *;omega) Y hY
  have hs:=hsep M ((le_max_right _ _).trans hM) g k L d (by unfold Stable;omega) hL hsmall Y hY
    e e e he he he hcusp hgenus hprof
  have hl:=hlinear M ((le_max_left _ _).trans hM) L hL e he hprev g k hg d Y hY (hsmall.le.trans hδ1)
  have hlinConv:(∑i∈Finset.Icc 1 L,Bl^i*e (L-i)) ≤ V:=by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (le_max_left _ _) i) (he _)
  have hsepConv:(∑i∈Finset.range L,if 2 ≤ i then Bs^i*(e (L-i)+e (L-i)+e (L-i)) else 0) ≤ 3*V:=by
    dsimp[V]
    rw[←Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_le_sum_of_injOn (fun i:ℕ=>i)
    · intro i hi j hj hij
      exact hij
    · intro j hj
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hj
      obtain ⟨hiL,hi2⟩:=Finset.mem_filter.mp hi
      exact Finset.mem_Icc.mpr ⟨by omega,(Finset.mem_range.mp hiL).le⟩
    · intro i hi
      have hp:Bs^i ≤ B^i:=pow_le_pow_left₀ hBs.le (le_max_right Bl Bs) i
      have hb:=mul_le_mul_of_nonneg_right hp (he (L-i))
      nlinarith
    · intro i hi hnot
      exact mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg (show 0 ≤ B by linarith) _) (he _))
  have hpowL:Bl^L ≤ B^L:=pow_le_pow_left₀ (by linarith) (le_max_left _ _) L
  have hpowS:Bs^L ≤ B^L:=pow_le_pow_left₀ hBs.le (le_max_right _ _) L
  have hl':|recursiveMerger P g k d Y+recursiveHandle P g k d Y-
      truncationValue (mergerSeries Y (formalHierarchyJet P Y) k d+nonseparatingSeries Y (formalHierarchyJet P Y) k d) L (1/h)| ≤
      Dl*S^(2*L-1)/h^L*(V+B^L):=by
    exact hl.trans (mul_le_mul_of_nonneg_left (add_le_add hlinConv hpowL) (by positivity))
  have hs':|recursiveSeparatingWeightedLow P g k L d Y+recursiveSeparatingWeightedCentral P g k L d Y-
      truncationValue (separatingSeries P Y (formalHierarchyJet P Y) (L-1) k d) L (1/h)| ≤
      3*Cs*S^(2*L-1)/h^L*(V+B^L):=by
    apply hs.trans
    have hforce:(∑i∈Finset.range L,if 2 ≤ i then Bs^i*(e (L-i)+e (L-i)+e (L-i)) else 0)+Bs^L ≤ 3*(V+B^L):=by
      have hp:0 ≤ B^L:=pow_nonneg (show 0 ≤ B by linarith) _
      linarith
    convert mul_le_mul_of_nonneg_left hforce (show 0 ≤ Cs*S^(2*L-1)/h^L by positivity) using 1 <;>ring
  rw[truncationValue_add]
  have hb:=(abs_add_le
    (recursiveMerger P g k d Y+recursiveHandle P g k d Y-truncationValue
      (mergerSeries Y (formalHierarchyJet P Y) k d+nonseparatingSeries Y (formalHierarchyJet P Y) k d) L (1/h))
    (recursiveSeparatingWeightedLow P g k L d Y+recursiveSeparatingWeightedCentral P g k L d Y-
      truncationValue (separatingSeries P Y (formalHierarchyJet P Y) (L-1) k d) L (1/h))).trans (add_le_add hl' hs')
  convert hb using 1 <;>dsimp[D,S,h,V] <;>ring
end WP.HigherOrder
