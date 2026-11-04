import WPFormalization.HigherOrder.OperatorRemainderStage
import WPFormalization.HigherOrder.RecursiveAdjacentSource
import WPFormalization.HigherOrder.AdjacentTruncation
import WPFormalization.HigherOrder.SmallWeightRegion
/-! Every-coordinate actual adjacent residual has the sharp edge bound.
The actual signed recursion and the genuine fixed hierarchy operator jet
are identified exactly. Small-weight geometry derives genus and degree
validity; no arbitrary-coordinate compatibility is assumed. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma profile_adjacent_remainder_step (P:PsiTheory) :
    ∃D B δ₀:ℝ,∃M₀:ℕ,0<D ∧ 1 ≤ B ∧ 0<δ₀ ∧ δ₀ ≤ 1 ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀L:ℕ,2 ≤ L→∀e:ℕ→ℝ,(∀q,0 ≤ e q)→
    (∀q:ℕ,1 ≤ q→q<L→∀s,RemainderStageBound P M s q (e q))→
    ∀g:ℕ,∀v:List ℕ,1 ≤ v.length→Stable g v.length→1 ≤ complexity g v.length→
    ∀Y∈Icc (0:ℝ) y₀,profileOrderWeight (M:ℝ) L v^2/(complexity g v.length:ℝ)<δ₀→
    ∀i:ℕ,i<v.length→
    |profile P g (raiseDegree v i) Y-profile P g v Y-
      canonicalAdjacentTruncation P Y L i v (1/(complexity g v.length:ℝ))| ≤
      D*profileOrderWeight (M:ℝ) L v^(2*L-1)/(complexity g v.length:ℝ)^L*
        ((∑j∈Finset.Icc 1 L,B^j*e (L-j))+B^L):=by
  obtain ⟨D,B,δ₀,M₀,hD,hB,hδ₀,hδ1,hM₀,hOp⟩:=recursive_operator_remainder_stage P
  refine ⟨D,B,δ₀,M₀,hD,hB,hδ₀,hδ1,hM₀,?_⟩
  intro M hM L hL e he hprev g v hv hs hh Y hY hsmall i hi
  let k:=v[i]!
  let d:=v.eraseIdx i
  have ht:k=v[i]:=by simp[k,List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hi]
  have hp0:(k::d).Perm v:=by simpa only[ht] using List.getElem_cons_eraseIdx_perm hi
  have hp1:(raiseDegree v i).Perm ((k+1)::d):=List.set_perm_cons_eraseIdx hi (k+1)
  have hlen:d.length+1=v.length:=by simpa only[List.length_cons] using hp0.length_eq
  have hw:profileOrderWeight (M:ℝ) L (k::d)=profileOrderWeight (M:ℝ) L v:=by
    unfold profileOrderWeight
    rw[hp0.sum_eq,hp0.length_eq]
  have hsmall1:profileOrderWeight (M:ℝ) L v^2/(complexity g v.length:ℝ)<1:=hsmall.trans_le hδ1
  have hM2:(2:ℝ) ≤ M:=by exact_mod_cast hM₀.trans hM
  have hS:(v.length:ℝ)+2*L ≤ profileOrderWeight (M:ℝ) L v:=by
    have hm:=mul_le_mul_of_nonneg_right hM2 (Nat.cast_nonneg L : (0:ℝ) ≤ L)
    dsimp[profileOrderWeight]
    linarith[Nat.cast_nonneg (α:=ℝ) v.sum]
  have hg:2 ≤ g:=by
    have ht:=small_weight_parent_genus_large g v.length L (profileOrderWeight (M:ℝ) L v)
      hv (by omega) hs hS hsmall1
    omega
  have hd: v.sum ≤ dimension g v.length:=by
    by_contra hn
    have hh':dimension g v.length<v.sum:=by omega
    have hb:=invalid_profile_large_weight (M:ℝ) (Nat.cast_nonneg _) L g v hh hh'
    linarith
  have hsource:=profile_adjacent_recursive_source P g k L d hg hL Y hY
    (profileOrderWeight (M:ℝ) L v) (by simpa only[hlen] using hS)
    (by simpa only[hlen] using hsmall1) (by simpa only[hp0.sum_eq,hlen] using hd)
  have hb:=hOp M hM L hL e he hprev g k hg d Y hY (by simpa only[hw,hlen] using hsmall)
  have heq:profile P g (raiseDegree v i) Y-profile P g v Y-
      canonicalAdjacentTruncation P Y L i v (1/(complexity g v.length:ℝ))=
      -(recursiveMerger P g k d Y+recursiveHandle P g k d Y+
        (recursiveSeparatingWeightedLow P g k L d Y+recursiveSeparatingWeightedCentral P g k L d Y)-
        truncationValue (mergerSeries Y (formalHierarchyJet P Y) k d+
          nonseparatingSeries Y (formalHierarchyJet P Y) k d+
          separatingSeries P Y (formalHierarchyJet P Y) (L-1) k d) L (1/(complexity g v.length:ℝ))):=by
    rw[canonicalAdjacentTruncation_eq_operators P Y L (by omega) i v]
    rw[profile_perm P g hp1 Y,←profile_perm P g hp0 Y]
    dsimp[k,d] at hsource ⊢
    linarith
  rw[heq,abs_neg]
  simpa only[hw,hlen] using hb
end WP.HigherOrder
