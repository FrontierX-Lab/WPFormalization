import WPFormalization.HigherOrder.MergerRemainderProof
import WPFormalization.HigherOrder.HandleRemainderProof
import WPFormalization.HigherOrder.RemainderStateBounds
import WPFormalization.HigherOrder.PreviousOrderConvolution
/-! Both actual linear recursion operators share one sharp edge remainder
row. Its only error input is the uniform strict previous-order four-stage
bound. Empty merger tails and all handle tails are included. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma truncationValue_add (f g:Series) (L:ℕ) (t:ℝ) :
    truncationValue (f+g) L t=truncationValue f L t+truncationValue g L t:=by
  simp only[truncationValue,map_add,add_mul,Finset.sum_add_distrib]
lemma recursive_linear_remainder_stage (P:PsiTheory) :
    ∃D B:ℝ,∃M₀:ℕ,0<D ∧ 1 ≤ B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀L:ℕ,2 ≤ L→∀e:ℕ→ℝ,(∀q,0 ≤ e q)→
    (∀q:ℕ,1 ≤ q→q<L→∀s,RemainderStageBound P M s q (e q))→
    ∀g k:ℕ,2 ≤ g→∀d:List ℕ,∀Y∈Icc (0:ℝ) y₀,
    profileOrderWeight (M:ℝ) L (k::d)^2/(complexity g (d.length+1):ℝ) ≤ 1→
    |recursiveMerger P g k d Y+recursiveHandle P g k d Y-
      truncationValue (mergerSeries Y (formalHierarchyJet P Y) k d+
        nonseparatingSeries Y (formalHierarchyJet P Y) k d) L (1/(complexity g (d.length+1):ℝ))| ≤
      D*profileOrderWeight (M:ℝ) L (k::d)^(2*L-1)/(complexity g (d.length+1):ℝ)^L*
        ((∑i∈Finset.Icc 1 L,B^i*e (L-i))+B^L):=by
  obtain ⟨Dm,Bm,Mm,hDm,hBm,hMm,hmerger⟩:=recursiveMerger_remainder_step P
  obtain ⟨Dh,Bh,Mh,hDh,hBh,hMh,hhandle⟩:=recursiveHandle_remainder_step P
  let B:=max 1 (max Bm Bh)
  let D:=3*(Dm+Dh)
  have hB:1 ≤ B:=le_max_left _ _
  have hBmB:Bm ≤ B:=(le_max_left _ _).trans (le_max_right _ _)
  have hBhB:Bh ≤ B:=(le_max_right _ _).trans (le_max_right _ _)
  refine ⟨D,B,max Mm Mh,by dsimp[D];positivity,hB,hMm.trans (le_max_left _ _),?_⟩
  intro M hM L hL e he hprev g k hg d Y hY hsmall
  have hMmM:Mm ≤ M:=(le_max_left _ _).trans hM
  have hMhM:Mh ≤ M:=(le_max_right _ _).trans hM
  let S:=profileOrderWeight (M:ℝ) L (k::d)
  let h:ℝ:=complexity g (d.length+1)
  let V:=∑i∈Finset.Icc 1 L,B^i*e (L-i)
  have hS:0 ≤ S:=by dsimp[S,profileOrderWeight];positivity
  have hh:0<h:=by dsimp[h];exact_mod_cast (show 0<complexity g (d.length+1) by unfold complexity;omega)
  have hV:0 ≤ V:=Finset.sum_nonneg (fun i hi=>mul_nonneg (pow_nonneg (by linarith) _) (he _))
  have hcusp (g' p' q:ℕ) (hp':1 ≤ p') (hs':Stable g' p') (hq:1 ≤ q) (hqL:q<L):
      |cuspCorrection P g' p' Y-truncationValue (formalCusp P Y p') q (1/(complexity g' p':ℝ))| ≤
        e q*scalarOrderWeight (M:ℝ) q p'^(2*q)/(complexity g' p':ℝ)^q:=by
    exact hprev q hq hqL 1 g' p' trivial hp' hs' (by unfold Stable complexity at *;omega) Y hY
  have hprof (g' q:ℕ) (hq:1 ≤ q) (hqL:q<L) (v:List ℕ) (hv:1 ≤ v.length) (hs':Stable g' v.length):
      |profile P g' v Y-truncationValue (formalProfile P Y v) q (1/(complexity g' v.length:ℝ))| ≤
        e q*profileOrderWeight (M:ℝ) q v^(2*q)/(complexity g' v.length:ℝ)^q:=by
    exact hprev q hq hqL 0 g' v hv hs' (by unfold Stable complexity at *;omega) Y hY
  have hgen (q:ℕ) (hq:1 ≤ q) (hqL:q<L):
      |genusCorrection P g (d.length+1) Y-truncationValue (formalGenus P Y (d.length+1)) q (1/h)| ≤
        e q*scalarOrderWeight (M:ℝ) q (d.length+1)^(2*q)/h^q:=by
    by_cases hp:d.length+1=1
    · exact hprev q hq hqL 3 g (d.length+1) hp (by omega) (by unfold Stable;omega) (by unfold complexity;omega) Y hY
    · exact hprev q hq hqL 2 g (d.length+1) (by omega) (by omega) (by unfold Stable;omega) (by unfold complexity;omega) Y hY
  have hmergerBound:|recursiveMerger P g k d Y-truncationValue (mergerSeries Y (formalHierarchyJet P Y) k d) L (1/h)| ≤
      3*Dm*S^(2*L-1)/h^L*(V+B^L):=by
    by_cases hd:1 ≤ d.length
    · have hb:=hmerger M hMmM g k L hg hL d hd Y hY hsmall (e (L-1)) (he _) e he
        (hcusp g d.length (L-1) hd (by unfold Stable;omega) (by omega) (by omega)) (by
          intro i hi hiL v hv
          have ht:=hprof g i hi (by omega) v (by omega) (by unfold Stable;omega)
          simpa only[hv] using ht)
      have hconv:=previous_order_linear_convolutions_bound Bm B hBm.le hB hBmB L (by omega) e he
      have hs0:0 ≤ ∑i∈Finset.range (L-1),Bm^i*e (L-1-i):=Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (he _))
      have hr:e (L-1)+(∑i∈Finset.range (L-1),Bm^i*e (L-1-i))+Bm^L ≤ 3*(V+B^L):=by
        have hp:0 ≤ B^L:=pow_nonneg (by linarith) _
        dsimp[V] at *
        linarith
      apply hb.trans
      convert mul_le_mul_of_nonneg_left hr (show 0 ≤ Dm*S^(2*L-1)/h^L by positivity) using 1 <;>ring
    · have hd0:d=[]:=List.length_eq_zero_iff.mp (by omega)
      subst d
      simp only[recursiveMerger,List.length_nil,Finset.range_zero,Finset.sum_empty,
        mergerSeries,mul_zero,truncationValue,map_zero,zero_mul,Finset.sum_const_zero,sub_self,abs_zero]
      positivity
  have hhandleBound:|recursiveHandle P g k d Y-truncationValue (nonseparatingSeries Y (formalHierarchyJet P Y) k d) L (1/h)| ≤
      3*Dh*S^(2*L-1)/h^L*(V+B^L):=by
    have hb:=hhandle M hMhM g k L hg hL d Y hY hsmall (e (L-1)) (he _) e e he he
      (hcusp (g-1) (d.length+2) (L-1) (by omega) (by unfold Stable;omega) (by omega) (by omega)) (by
        intro i hi hiL v hv
        have ht:=hprof (g-1) i hi (by omega) v (by omega) (by unfold Stable;omega)
        simpa only[hv] using ht) (fun i hi hiL=>hgen i hi (by omega))
    have hconv:=previous_order_linear_convolutions_bound Bh B hBh.le hB hBhB L (by omega) e he
    have hp:0 ≤ B^L:=pow_nonneg (by linarith) _
    have hr:e (L-1)+(∑i∈Finset.range (L-1),Bh^i*e (L-1-i))+
        (∑i∈Finset.range (L-1),Bh^i*e (L-1-i))+Bh^L ≤ 3*(V+B^L):=by dsimp[V] at *;linarith
    apply hb.trans
    convert mul_le_mul_of_nonneg_left hr (show 0 ≤ Dh*S^(2*L-1)/h^L by positivity) using 1 <;>ring
  rw[truncationValue_add]
  have hb:= (abs_add_le
    (recursiveMerger P g k d Y-truncationValue (mergerSeries Y (formalHierarchyJet P Y) k d) L (1/h))
    (recursiveHandle P g k d Y-truncationValue (nonseparatingSeries Y (formalHierarchyJet P Y) k d) L (1/h))).trans
    (add_le_add hmergerBound hhandleBound)
  convert hb using 1 <;>dsimp[D,S,h,V] <;>ring
end WP.HigherOrder
