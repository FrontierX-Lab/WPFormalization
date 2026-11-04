import WPFormalization.HigherOrder.RecursiveMerger
import WPFormalization.HigherOrder.MergerAtomRemainder
import WPFormalization.HigherOrder.WeightedRemainderBounds
import WPFormalization.Analysis.NormalizedMomentScale
/-! The actual all-order merger remainder step. Only already lower-order
actual cusp/profile remainders are induction inputs. C.4 coefficient
bounds, shifts, genuine kernel moments, formal summation, original deficit
support and the finite label count are instantiated before the conclusion.
The sharp S_L^(2L-1) edge scale is retained for the canonical path step. -/
noncomputable section
open Set
namespace WP.HigherOrder
lemma recursiveMerger_remainder_step (P:PsiTheory) :
    ∃D B:ℝ,∃M₀:ℕ,0<D ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g k L:ℕ,2 ≤ g→2 ≤ L→∀d:List ℕ,1 ≤ d.length→
    ∀Y∈Icc (0:ℝ) y₀,profileOrderWeight (M:ℝ) L (k::d)^2/(complexity g (d.length+1):ℝ) ≤ 1→
    ∀Cq:ℝ,0 ≤ Cq→∀E:ℕ→ℝ,(∀i:ℕ,0 ≤ E i)→
    (|cuspCorrection P g d.length Y-truncationValue (formalCusp P Y d.length) (L-1) (1/(complexity g d.length:ℝ))| ≤
      Cq*scalarOrderWeight (M:ℝ) (L-1) d.length^(2*(L-1))/(complexity g d.length:ℝ)^(L-1))→
    (∀i:ℕ,1 ≤ i→i ≤ L-1→∀v:List ℕ,v.length=d.length→
      |profile P g v Y-truncationValue (formalProfile P Y v) i (1/(complexity g d.length:ℝ))| ≤
      E i*profileOrderWeight (M:ℝ) i v^(2*i)/(complexity g d.length:ℝ)^i)→
    |recursiveMerger P g k d Y-truncationValue (mergerSeries Y (formalHierarchyJet P Y) k d) L
      (1/(complexity g (d.length+1):ℝ))| ≤
      D*profileOrderWeight (M:ℝ) L (k::d)^(2*L-1)/(complexity g (d.length+1):ℝ)^L*
        (Cq+∑i∈Finset.range (L-1),B^i*E (L-1-i)+B^L) :=by
  obtain ⟨Da,B,Ma,hDa,hB,hMa,hAtom⟩:=actual_merger_atom_remainder_step_exponential P
  obtain ⟨Cm,Mm,hCm,hMm,hmom⟩:=Analysis.canonical_growing_order_scale_bounds
  let M₀:ℕ:=max Ma ⌈Mm⌉₊
  have hM₀:2 ≤ M₀:=hMa.trans (le_max_left _ _)
  refine ⟨2*Cm*Da,B,M₀,by positivity,hB,hM₀,?_⟩
  intro M hM g k L hg hL d hd Y hY hsmall Cq hCq E hE hCs hPs
  have hMsource:Ma ≤ M:=(le_max_left _ _).trans hM
  have hMmom:Mm ≤ (M:ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hM))
  have hMtwo:(2:ℝ) ≤ M:=by exact_mod_cast (hM₀.trans hM)
  let S:=profileOrderWeight (M:ℝ) L (k::d)
  let h:ℝ:=complexity g (d.length+1)
  let R:=Cq+∑i∈Finset.range (L-1),B^i*E (L-1-i)+B^L
  have hR:0 ≤ R:=by
    dsimp[R]
    exact add_nonneg (add_nonneg hCq (Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (hE _)))) (by positivity)
  have hh:0<h:=by dsimp[h];exact_mod_cast (show 0<complexity g (d.length+1) by unfold complexity;omega)
  have hn:0<(complexity g d.length:ℝ):=by exact_mod_cast (show 0<complexity g d.length by unfold complexity;omega)
  have hnR:(complexity g d.length:ℝ)=h-1:=by
    have hc:complexity g d.length+1=complexity g (d.length+1):=by unfold complexity;omega
    have he:((complexity g d.length:ℝ)+1)=h:=by
      dsimp[h]
      exact_mod_cast hc
    linarith
  have hS:2*(L:ℝ) ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hMtwo (Nat.cast_nonneg L : (0:ℝ) ≤ L)
    dsimp[S,profileOrderWeight]
    linarith[Nat.cast_nonneg (α:=ℝ) (k::d).sum,Nat.cast_nonneg (α:=ℝ) (k::d).length]
  have hSp:0<S:=by
    have hLR:(2:ℝ) ≤ L:=by exact_mod_cast hL
    linarith
  have hpow:0 ≤ Da*R/h^L:=by positivity
  have hmoment:=hmom (M:ℝ) hMmom L (k::d).sum (k::d).length (2*(L-1)) (by simp) (by omega) Y hY
  have hws:Summable (fun l:ℕ=>(S+l+1)^(2*(L-1))*|weight Y l|):=hmoment.1
  have hwb:(∑'l:ℕ,(S+l+1)^(2*(L-1))*|weight Y l|) ≤ Cm*S^(2*(L-1)):=hmoment.2.2.1
  have hscalar (l:ℕ):scalarOrderWeight (M:ℝ) (L-1) d.length ≤ S+l+1:=by
    have hm:=mul_le_mul_of_nonneg_left (show ((L-1:ℕ):ℝ) ≤ L by exact_mod_cast (Nat.sub_le L 1)) (Nat.cast_nonneg M : (0:ℝ) ≤ M)
    dsimp[S,scalarOrderWeight,profileOrderWeight]
    simp only[List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith[Nat.cast_nonneg (α:=ℝ) k,Nat.cast_nonneg (α:=ℝ) d.sum,Nat.cast_nonneg (α:=ℝ) l]
  have hprofileWeight (j l i:ℕ) (hj:j<d.length) (hi:i ≤ L-1):
      profileOrderWeight (M:ℝ) i (mergerProfile k d l j) ≤ S+l+1:=by
    have hsum:((mergerProfile k d l j).sum:ℝ) ≤ ((k::d).sum:ℝ)+l:=by exact_mod_cast mergerProfile_sum_weak k l j d hj
    have hm:=mul_le_mul_of_nonneg_left (show (i:ℝ) ≤ L by exact_mod_cast (hi.trans (Nat.sub_le L 1))) (Nat.cast_nonneg M : (0:ℝ) ≤ M)
    dsimp[S,profileOrderWeight]
    rw[mergerProfile_length_exact k l j d hj]
    simp only[List.sum_cons,Nat.cast_add] at hsum
    simp only[List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith
  have hpoint (j:ℕ) (hj:j<d.length) (l:ℕ):
      |mergerAtomValue P g k d Y j l-truncationValue (mergerAtomSeries P Y k d j l) L (1/h)| ≤
        (Da*R/h^L)*(S+l+1)^(2*(L-1)):=by
    unfold mergerAtomValue mergerAtomSeries
    split_ifs with hguard
    · have hcuspT:|cuspCorrection P g d.length Y-truncationValue (formalCusp P Y d.length) (L-1) (1/(h-1))| ≤
          Cq*(S+l+1)^(2*(L-1))/(h-1)^(L-1):=by
        rw[←hnR]
        apply hCs.trans
        apply div_le_div_of_nonneg_right _ (pow_nonneg hn.le _)
        apply mul_le_mul_of_nonneg_left _ hCq
        exact pow_le_pow_left₀ (by unfold scalarOrderWeight;positivity) (hscalar l) _
      have hprofT (i:ℕ) (hi:1 ≤ i) (hiL:i ≤ L-1):
          |profile P g (mergerProfile k d l j) Y-truncationValue (formalProfile P Y (mergerProfile k d l j)) i (1/(h-1))| ≤
            E i*(S+l+1)^(2*i)/(h-1)^i:=by
        rw[←hnR]
        apply (hPs i hi hiL _ (mergerProfile_length_exact k l j d hj)).trans
        apply div_le_div_of_nonneg_right _ (pow_nonneg hn.le _)
        apply mul_le_mul_of_nonneg_left _ (hE i)
        exact pow_le_pow_left₀ (by unfold profileOrderWeight;positivity) (hprofileWeight j l i hj hiL) _
      have hsT:S ≤ S+l+1:=by linarith[Nat.cast_nonneg (α:=ℝ) l]
      have hb:=hAtom M hMsource g (d.length+1) L hg (by omega) hL (mergerProfile k d l j)
        (by rw[mergerProfile_length_exact k l j d hj];omega) S (S+l+1) hS hsT
        (by simpa only[Nat.add_sub_cancel] using hscalar l) (hprofileWeight j l (L-1) hj le_rfl)
        hsmall Y hY Cq hCq E hE (by simpa only[Nat.add_sub_cancel] using hcuspT) hprofT
      simpa only[Nat.add_sub_cancel,h,R,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hb
    · simp only[truncationValue,map_zero,zero_mul,Finset.sum_const_zero,sub_self,abs_zero]
      positivity
  have hjbound (j:ℕ) (hj:j∈Finset.range d.length):
      |(∑'l:ℕ,weight Y l*mergerAtomValue P g k d Y j l)-
        truncationValue (coefficientSum (fun l=>PowerSeries.C (weight Y l)*mergerAtomSeries P Y k d j l)) L (1/h)| ≤
      Cm*(Da*R/h^L)*S^(2*(L-1)):=by
    exact weighted_actual_remainder_bound (weight Y)
      (fun l=>mergerAtomValue P g k d Y j l-truncationValue (mergerAtomSeries P Y k d j l) L (1/h))
      _ S (Da*R/h^L) Cm (2*(L-1)) hpow (merger_atom_remainder_hasSum P g k j L d hg (Finset.mem_range.mp hj) Y (1/h) hY)
      hws hwb (hpoint j (Finset.mem_range.mp hj))
  rw[recursiveMerger_remainder_identity P g k L d Y (1/h) hY]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*(Cm*(Da*R/h^L)*S^(2*(L-1))):=by
      apply Finset.sum_le_sum
      intro j hj
      rw[abs_mul,abs_of_nonneg (by positivity:(0:ℝ) ≤ 2*(d[j]!:ℝ)+1)]
      exact mul_le_mul_of_nonneg_left (hjbound j hj) (by positivity)
    _=(∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1))*(Cm*(Da*R/h^L)*S^(2*(L-1))):=by rw[Finset.sum_mul]
    _ ≤ (2*S)*(Cm*(Da*R/h^L)*S^(2*(L-1))):=mul_le_mul_of_nonneg_right
      (merger_count_le_order_weight (M:ℝ) (Nat.cast_nonneg _) L k d) (by positivity)
    _=_:=by
      have hp:S*S^(2*(L-1))=S^(2*L-1):=by rw[←pow_succ'];congr 1;omega
      calc
        _=(2*Cm*Da)*(S*S^(2*(L-1)))/h^L*R:=by ring
        _=_:=by rw[hp]

end WP.HigherOrder
