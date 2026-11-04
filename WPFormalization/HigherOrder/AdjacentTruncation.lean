import WPFormalization.HigherOrder.FixedPathRemainder
/-! Finite adjacent jets coincide with the actual three recursive operator jets.
This identity uses the prescribed fixed path and does not assume all-coordinate compatibility. -/

noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma separatingSeries_coeff_cutoff (P:PsiTheory) (Y:ℝ) (F:HierarchyJet)
    (K n t:ℕ) (d:List ℕ) (hn:n≤K) :
    PowerSeries.coeff n (separatingSeries P Y F K t d)=
      PowerSeries.coeff n (separatingSeries P Y F n t d) := by
  let Q (j:ℕ) (I:Finset ℕ):Series:=ratioSeries Y F (d.length+1) j I.card*
    coefficientSum (fun l=>C (weight Y l)*∑u∈Finset.range (t+l-1),
      C (smallW P Y j (u::selectedNat d I))*complexityShift (2*j+I.card)
        (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))
  have hterm (j:ℕ) (I:Finset ℕ) :
      PowerSeries.coeff n (if Stable j (I.card+1) ∧ 2≤2*j+I.card ∧ 2*j+I.card≤K then Q j I else 0)=
      PowerSeries.coeff n (if Stable j (I.card+1) ∧ 2≤2*j+I.card ∧ 2*j+I.card≤n then Q j I else 0) := by
    by_cases hr:2*j+I.card≤n
    · have he : (Stable j (I.card+1) ∧ 2≤2*j+I.card ∧ 2*j+I.card≤K)=
          (Stable j (I.card+1) ∧ 2≤2*j+I.card ∧ 2*j+I.card≤n) := by
        apply propext
        constructor <;> intro h
        · exact ⟨h.1,h.2.1,hr⟩
        · exact ⟨h.1,h.2.1,hr.trans hn⟩
      simp only[he]
    · have hz:PowerSeries.coeff n (Q j I)=0:=by
        dsimp[Q]
        rw[ratioSeries_mul_coeff,ite_eq_right hr]
      split_ifs <;> simp only[hz,map_zero]
  unfold separatingSeries
  simp only[map_sum]
  change (∑j∈Finset.range (K+1),∑I∈(Finset.range d.length).powerset,
    PowerSeries.coeff n (if Stable j (I.card+1) ∧ 2≤2*j+I.card ∧ 2*j+I.card≤K then Q j I else 0))=_
  simp_rw[hterm]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hjn
  apply Finset.sum_eq_zero
  intro I hI
  have hj':n<j:=by
    have hh:¬j<n+1:=by simpa only[Finset.mem_range] using hjn
    omega
  rw[ite_eq_right (by omega : ¬(Stable j (I.card+1) ∧ 2≤2*j+I.card ∧ 2*j+I.card≤n)),map_zero]

lemma adjacent_operator_constant (P:PsiTheory) (Y:ℝ) (F:HierarchyJet)
    (K t:ℕ) (d:List ℕ) :
    PowerSeries.coeff 0 (mergerSeries Y F t d+nonseparatingSeries Y F t d+
      separatingSeries P Y F K t d)=0 := by
  have hs:=separatingSeries_coeff_cutoff P Y F K 0 t d (Nat.zero_le K)
  have hz:PowerSeries.coeff 0 (separatingSeries P Y F 0 t d)=0 := by
    unfold separatingSeries
    simp only[Nat.reduceAdd,Finset.sum_range_one,map_sum]
    apply Finset.sum_eq_zero
    intro I hI
    rw[ite_eq_right (by omega : ¬(Stable 0 (I.card+1) ∧ 2≤2*0+I.card ∧ 2*0+I.card≤0)),map_zero]
  rw[map_add,map_add,hs,hz]
  simp only[PowerSeries.coeff_zero_eq_constantCoeff,mergerSeries,nonseparatingSeries,
    map_mul,shiftVariable_constant,mul_zero,zero_mul,add_zero]

lemma canonicalAdjacentTruncation_eq_operators (P:PsiTheory) (Y:ℝ) (L:ℕ) (hL:1≤L)
    (i:ℕ) (d:List ℕ) (t:ℝ) :
    canonicalAdjacentTruncation P Y L i d t=
      -truncationValue (mergerSeries Y (formalHierarchyJet P Y) (d[i]!) (d.eraseIdx i)+
        nonseparatingSeries Y (formalHierarchyJet P Y) (d[i]!) (d.eraseIdx i)+
        separatingSeries P Y (formalHierarchyJet P Y) (L-1) (d[i]!) (d.eraseIdx i)) L t := by
  let F:=formalHierarchyJet P Y
  let O:=mergerSeries Y F (d[i]!) (d.eraseIdx i)+nonseparatingSeries Y F (d[i]!) (d.eraseIdx i)+
    separatingSeries P Y F (L-1) (d[i]!) (d.eraseIdx i)
  have h0:PowerSeries.coeff 0 O=0:=adjacent_operator_constant P Y F (L-1) _ _
  have ht : truncationValue O L t=
      ∑j∈Finset.range (L-1),PowerSeries.coeff (j+1) O*t^(j+1) := by
    unfold truncationValue
    conv_lhs=>rw[show L=(L-1)+1 by omega,Finset.sum_range_succ']
    simp only[h0,pow_zero,mul_one,add_zero]
  change _= -truncationValue O L t
  rw[ht,←Finset.sum_neg_distrib]
  unfold canonicalAdjacentTruncation
  apply Finset.sum_congr rfl
  intro j hj
  have hj':j+1≤L-1:=by have hh:=Finset.mem_range.mp hj;omega
  dsimp[adjacentCoefficient,O,F]
  rw[map_add,map_add,map_add,map_add,
    separatingSeries_coeff_cutoff P Y (formalHierarchyJet P Y) (L-1) (j+1) _ _ hj']
  ring
end WP.HigherOrder
