import WPFormalization.HigherOrder.RecursiveHandle
import WPFormalization.HigherOrder.HandleAtomRemainder
import WPFormalization.HigherOrder.WeightedRemainderBounds
import WPFormalization.Analysis.NormalizedMomentScale
/-! The full actual handle remainder step at every order. Empty marking
tails are included. The genuine shifted cusp/profile/genus atom bound,
normal convergence, finite deficit support, node count and uniform kernel
moment are instantiated; only strict previous-order actual errors remain.
The sharp S_L^(2L-1) edge scale is retained for the fixed coordinate path. -/
noncomputable section
set_option maxHeartbeats 0
open Set
namespace WP.HigherOrder
lemma recursiveHandle_remainder_step (P:PsiTheory) :
    ∃D B:ℝ,∃M₀:ℕ,0<D ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g k L:ℕ,2 ≤ g→2 ≤ L→∀d:List ℕ,∀Y∈Icc (0:ℝ) y₀,
    profileOrderWeight (M:ℝ) L (k::d)^2/(complexity g (d.length+1):ℝ) ≤ 1→
    ∀Cq:ℝ,0 ≤ Cq→∀E H:ℕ→ℝ,(∀i:ℕ,0 ≤ E i)→(∀i:ℕ,0 ≤ H i)→
    (|cuspCorrection P (g-1) (d.length+2) Y-truncationValue (formalCusp P Y (d.length+2)) (L-1) (1/(complexity (g-1) (d.length+2):ℝ))| ≤
      Cq*scalarOrderWeight (M:ℝ) (L-1) (d.length+2)^(2*(L-1))/(complexity (g-1) (d.length+2):ℝ)^(L-1))→
    (∀i:ℕ,1 ≤ i→i ≤ L-1→∀v:List ℕ,v.length=d.length+2→
      |profile P (g-1) v Y-truncationValue (formalProfile P Y v) i (1/(complexity (g-1) (d.length+2):ℝ))| ≤
      E i*profileOrderWeight (M:ℝ) i v^(2*i)/(complexity (g-1) (d.length+2):ℝ)^i)→
    (∀i:ℕ,1 ≤ i→i ≤ L-1→
      |genusCorrection P g (d.length+1) Y-truncationValue (formalGenus P Y (d.length+1)) i (1/(complexity g (d.length+1):ℝ))| ≤
      H i*scalarOrderWeight (M:ℝ) i (d.length+1)^(2*i)/(complexity g (d.length+1):ℝ)^i)→
    |recursiveHandle P g k d Y-truncationValue (nonseparatingSeries Y (formalHierarchyJet P Y) k d) L
      (1/(complexity g (d.length+1):ℝ))| ≤
      D*profileOrderWeight (M:ℝ) L (k::d)^(2*L-1)/(complexity g (d.length+1):ℝ)^L*
        (Cq+∑i∈Finset.range (L-1),B^i*E (L-1-i)+∑i∈Finset.range (L-1),B^i*H (L-1-i)+B^L) :=by
  obtain ⟨Da,B,Ma,hDa,hB,hMa,hAtom⟩:=actual_handle_atom_remainder_step_exponential P
  obtain ⟨Cm,Mm,hCm,hMm,hmom⟩:=Analysis.canonical_growing_order_scale_bounds
  let M₀:ℕ:=max Ma ⌈Mm⌉₊
  have hM₀:2 ≤ M₀:=hMa.trans (le_max_left _ _)
  refine ⟨Cm*Da,B,M₀,by positivity,hB,hM₀,?_⟩
  intro M hM g k L hg hL d Y hY hsmall Cq hCq E H hE hH hCs hPs hGs
  have hMsource:Ma ≤ M:=(le_max_left _ _).trans hM
  have hMmom:Mm ≤ (M:ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hM))
  have hMtwo:(2:ℝ) ≤ M:=by exact_mod_cast (hM₀.trans hM)
  let S:=profileOrderWeight (M:ℝ) L (k::d)
  let h:ℝ:=complexity g (d.length+1)
  let R:=Cq+∑i∈Finset.range (L-1),B^i*E (L-1-i)+∑i∈Finset.range (L-1),B^i*H (L-1-i)+B^L
  have hR:0 ≤ R:=by
    dsimp[R]
    exact add_nonneg (add_nonneg (add_nonneg hCq (Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (hE _))))
      (Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (hH _)))) (by positivity)
  have hh:0<h:=by dsimp[h];exact_mod_cast (show 0<complexity g (d.length+1) by unfold complexity;omega)
  have hn:0<(complexity (g-1) (d.length+2):ℝ):=by exact_mod_cast (show 0<complexity (g-1) (d.length+2) by unfold complexity;omega)
  have hnR:(complexity (g-1) (d.length+2):ℝ)=h-1:=by
    have hc:complexity (g-1) (d.length+2)+1=complexity g (d.length+1):=by unfold complexity;omega
    have he:((complexity (g-1) (d.length+2):ℝ)+1)=h:=by dsimp[h];exact_mod_cast hc
    linarith
  have hS:2*(L:ℝ) ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hMtwo (Nat.cast_nonneg L : (0:ℝ) ≤ L)
    dsimp[S,profileOrderWeight]
    linarith[Nat.cast_nonneg (α:=ℝ) (k::d).sum,Nat.cast_nonneg (α:=ℝ) (k::d).length]
  have hSp:0<S:=by
    have hLR:(2:ℝ) ≤ L:=by exact_mod_cast hL
    linarith
  have hg3:3 ≤ g:=by
    by_contra hnot
    have hg2:g=2:=by omega
    have hSbig:(d.length:ℝ)+5 ≤ S:=by
      have hm:=mul_le_mul hMtwo (show (2:ℝ) ≤ L by exact_mod_cast hL) (by norm_num) (by positivity:(0:ℝ) ≤ M)
      dsimp[S,profileOrderWeight]
      simp only[List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith[Nat.cast_nonneg (α:=ℝ) k,Nat.cast_nonneg (α:=ℝ) d.sum]
    have hheq:h=(d.length:ℝ)+3:=by
      dsimp[h]
      rw[hg2]
      have hn:complexity 2 (d.length+1)=d.length+3:=by unfold complexity;omega
      rw[hn,Nat.cast_add,Nat.cast_ofNat]
    have hsq:S^2 ≤ h:=(div_le_one hh).mp hsmall
    nlinarith[Nat.cast_nonneg (α:=ℝ) d.length]
  have hpow:0 ≤ Da*R/h^L:=by positivity
  have hmoment:=hmom (M:ℝ) hMmom L (k::d).sum (k::d).length (2*L-1) (by simp) (by omega) Y hY
  have hws:Summable (fun l:ℕ=>(S+l+1)^(2*L-1)*|weight Y l|):=hmoment.1
  have hwb:(∑'l:ℕ,(S+l+1)^(2*L-1)*|weight Y l|) ≤ Cm*S^(2*L-1):=hmoment.2.2.1
  have hscalar (l:ℕ):scalarOrderWeight (M:ℝ) (L-1) (d.length+2) ≤ S+l+1:=by
    have hm:=mul_le_mul_of_nonneg_right hMtwo (by norm_num:(0:ℝ) ≤ 1)
    have hML:(M:ℝ)*((L-1:ℕ):ℝ)+(M:ℝ)=(M:ℝ)*L:=by
      have he:((L-1:ℕ):ℝ)+1=(L:ℝ):=by exact_mod_cast (show L-1+1=L by omega)
      nlinarith
    dsimp[S,scalarOrderWeight,profileOrderWeight]
    simp only[List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    linarith[Nat.cast_nonneg (α:=ℝ) k,Nat.cast_nonneg (α:=ℝ) d.sum,Nat.cast_nonneg (α:=ℝ) l]
  have hprofileWeight (l u i:ℕ) (hu:u<k+l-1) (hi:i ≤ L-1):
      profileOrderWeight (M:ℝ) i (contractionProfile k d l u) ≤ S+l+1:=by
    have hsum:((contractionProfile k d l u).sum:ℝ) ≤ ((k::d).sum:ℝ)+l:=by exact_mod_cast contractionProfile_sum_weak k l u d hu
    have hm:=mul_le_mul_of_nonneg_left (show (i:ℝ) ≤ L by exact_mod_cast (hi.trans (Nat.sub_le L 1))) (Nat.cast_nonneg M : (0:ℝ) ≤ M)
    dsimp[S,profileOrderWeight]
    rw[contractionProfile_length_exact]
    simp only[List.sum_cons,Nat.cast_add] at hsum
    simp only[List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    linarith
  have hgenusWeight (l i:ℕ) (hi:i ≤ L-1):scalarOrderWeight (M:ℝ) i (d.length+1) ≤ S+l+1:=by
    have hm:=mul_le_mul_of_nonneg_left (show (i:ℝ) ≤ L by exact_mod_cast (hi.trans (Nat.sub_le L 1))) (Nat.cast_nonneg M : (0:ℝ) ≤ M)
    dsimp[S,scalarOrderWeight,profileOrderWeight]
    simp only[List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith[Nat.cast_nonneg (α:=ℝ) k,Nat.cast_nonneg (α:=ℝ) d.sum,Nat.cast_nonneg (α:=ℝ) l]
  have hpoint (l u:ℕ) (hu:u<k+l-1):
      |handleAtomValue P g k d Y l u-truncationValue (handleAtomSeries P Y k d l u) L (1/h)| ≤
        (Da*R/h^L)*(S+l+1)^(2*(L-1)):=by
    have hcuspT:|cuspCorrection P (g-1) (d.length+2) Y-truncationValue (formalCusp P Y (d.length+2)) (L-1) (1/(h-1))| ≤
        Cq*(S+l+1)^(2*(L-1))/(h-1)^(L-1):=by
      rw[←hnR]
      apply hCs.trans
      apply div_le_div_of_nonneg_right _ (pow_nonneg hn.le _)
      apply mul_le_mul_of_nonneg_left _ hCq
      exact pow_le_pow_left₀ (by unfold scalarOrderWeight;positivity) (hscalar l) _
    have hprofT (i:ℕ) (hi:1 ≤ i) (hiL:i ≤ L-1):
        |profile P (g-1) (contractionProfile k d l u) Y-truncationValue (formalProfile P Y (contractionProfile k d l u)) i (1/(h-1))| ≤
          E i*(S+l+1)^(2*i)/(h-1)^i:=by
      rw[←hnR]
      apply (hPs i hi hiL _ (contractionProfile_length_exact k l u d)).trans
      apply div_le_div_of_nonneg_right _ (pow_nonneg hn.le _)
      apply mul_le_mul_of_nonneg_left _ (hE i)
      exact pow_le_pow_left₀ (by unfold profileOrderWeight;positivity) (hprofileWeight l u i hu hiL) _
    have hgenT (i:ℕ) (hi:1 ≤ i) (hiL:i ≤ L-1):
        |genusCorrection P g (d.length+1) Y-truncationValue (formalGenus P Y (d.length+1)) i (1/h)| ≤ H i*(S+l+1)^(2*i)/h^i:=by
      apply (hGs i hi hiL).trans
      apply div_le_div_of_nonneg_right _ (pow_nonneg hh.le _)
      apply mul_le_mul_of_nonneg_left _ (hH i)
      exact pow_le_pow_left₀ (by unfold scalarOrderWeight;positivity) (hgenusWeight l i hiL) _
    have hsT:S ≤ S+l+1:=by linarith[Nat.cast_nonneg (α:=ℝ) l]
    have hb:=hAtom M hMsource g (d.length+1) L hg3 (by omega) hL (contractionProfile k d l u)
      (by simp only[contractionProfile_length_exact,Nat.add_assoc]) S (S+l+1) hS hsT (by simpa only[Nat.add_assoc] using hscalar l)
      (hprofileWeight l u (L-1) hu le_rfl) hsmall Y hY Cq hCq E H hE hH
      (by simpa only[Nat.add_assoc] using hcuspT) hprofT hgenT
    simpa only[handleAtomValue,handleAtomSeries,Nat.add_assoc,h,R,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hb
  have hlayer (l:ℕ):
      |handleLayerValue P g k d Y l-truncationValue (handleLayerSeries P Y k d l) L (1/h)| ≤
        (Da*R/h^L)*(S+l+1)^(2*L-1):=by
    rw[handleLayerSeries,truncationValue_finset_sum,handleLayerValue,←Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑u∈Finset.range (k+l-1),(Da*R/h^L)*(S+l+1)^(2*(L-1)):=Finset.sum_le_sum (fun u hu=>hpoint l u (Finset.mem_range.mp hu))
      _=((k+l-1:ℕ):ℝ)*((Da*R/h^L)*(S+l+1)^(2*(L-1))):=by simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      _ ≤ (S+l+1)*((Da*R/h^L)*(S+l+1)^(2*(L-1))):=by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hpow (pow_nonneg (by linarith[Nat.cast_nonneg (α:=ℝ) l]) _))
        have hn:(k+l-1:ℕ) ≤ k+l:=Nat.sub_le _ _
        have hnR:((k+l-1:ℕ):ℝ) ≤ (k:ℝ)+l:=by exact_mod_cast hn
        have hML:0 ≤ (M:ℝ)*(L:ℝ):=by positivity
        dsimp[S,profileOrderWeight]
        simp only[List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        linarith[Nat.cast_nonneg (α:=ℝ) d.sum,Nat.cast_nonneg (α:=ℝ) d.length]
      _=_:=by
        have hp:(S+l+1)*(S+l+1)^(2*(L-1))=(S+l+1)^(2*L-1):=by rw[←pow_succ'];congr 1;omega
        calc
          _=(Da*R/h^L)*((S+l+1)*(S+l+1)^(2*(L-1))):=by ring
          _=_:=by rw[hp]
  have hb:=weighted_actual_remainder_bound (weight Y)
    (fun l=>handleLayerValue P g k d Y l-truncationValue (handleLayerSeries P Y k d l) L (1/h))
    _ S (Da*R/h^L) Cm (2*L-1) hpow (handle_layer_remainder_hasSum P g k L d hg Y (1/h) hY) hws hwb hlayer
  convert hb using 1 <;>dsimp[h,R] <;>ring
end WP.HigherOrder
