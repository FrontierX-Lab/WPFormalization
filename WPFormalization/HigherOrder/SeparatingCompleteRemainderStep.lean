import WPFormalization.HigherOrder.SeparatingRemainderStep
import WPFormalization.HigherOrder.SeparatingCentralRemainder
import WPFormalization.HigherOrder.SeparatingRemainderIdentity
/-! The full separating source has one strict-loss remainder row.
The actual low weighted source is paired exactly with the prescribed C.16
finite jet by genuine HasSum/cardinality reindexing. The real C.5 central
forcing is added on a fixed small-weight region. All error inputs have
strictly smaller truncation order; loss 2 and S_L^(2L-1) are retained. -/
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries

lemma recursiveSeparatingWeightedLow_error_eq_card (P:PsiTheory)(g t L:ℕ)(d:List ℕ)
    (hL:1 ≤ L)(Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(S:ℝ)(hs:Stable g (d.length+1))
    (hS:((d.length+1:ℕ):ℝ)+2*L ≤ S)(hsmall:S^2/(complexity g (d.length+1):ℝ)<1) :
    recursiveSeparatingWeightedLow P g t L d Y-
      truncationValue (separatingSeries P Y (formalHierarchyJet P Y) (L-1) t d) L (1/(complexity g (d.length+1):ℝ))=
      separatingLowRemainder P g t L d Y := by
  rw[recursiveSeparatingWeightedLow_remainder_identity P g t L d hL Y _ hY S hs hS hsmall]
  unfold separatingLowRemainder
  apply Finset.sum_congr rfl
  intro j hj
  rw[ComplexCanonical.sum_powerset_by_card_truncated (Finset.range d.length) d.length _ (by
    intro I hI hcard
    have hh:=Finset.card_le_card (Finset.mem_powerset.mp hI)
    simp only[Finset.card_range] at hh
    omega)]
  apply Finset.sum_congr rfl
  intro s hsRange
  by_cases hguard:Stable j (s+1) ∧ 2 ≤ 2*j+s ∧ 2*j+s<L
  · rw[ite_eq_left hguard]
    have hs':s<d.length+1:=Finset.mem_range.mp hsRange
    have hv:=small_weight_split_child_valid g (d.length+1) j s L S (by omega) hL hs hS hsmall (by omega) hs'
    have hguard':Stable j (s+1) ∧ 2 ≤ 2*j+s ∧ 2*j+s ≤ L-1:=
      ⟨hguard.1,hguard.2.1,by omega⟩
    have hsum:∀I∈Finset.powersetCard s (Finset.range d.length),Summable (fun l:ℕ=>weight Y l*
        (separatingAtomValue P g t d Y j I l-truncationValue (separatingAtomSeries P Y t d j I l) L (1/(complexity g (d.length+1):ℝ)))):=by
      intro I hI
      have hsub:=(Finset.mem_powersetCard.mp hI).1
      have hc:=(Finset.mem_powersetCard.mp hI).2
      exact (separating_atom_remainder_hasSum P g t j L d I hsub hv.1
        (by simpa only[hc] using hguard.1) (by simpa only[hc] using hv.2) Y _ hY).summable
    have hPull:=Summable.tsum_finsetSum hsum
    unfold separatingCardinalityRemainder
    simp_rw[Finset.mul_sum]
    rw[hPull]
    apply Finset.sum_congr rfl
    intro I hI
    have hc:=(Finset.mem_powersetCard.mp hI).2
    simp only[hc,ite_eq_left hguard']
  · rw[ite_eq_right hguard]
    apply Finset.sum_eq_zero
    intro I hI
    have hc:=(Finset.mem_powersetCard.mp hI).2
    have hg':¬(Stable j (s+1) ∧ 2 ≤ 2*j+s ∧ 2*j+s ≤ L-1):=by
      intro h
      apply hguard
      exact ⟨h.1,h.2.1,by omega⟩
    rw[hc,ite_eq_right hg']

lemma recursiveSeparating_uniform_remainder_step (P:PsiTheory) :
    ∃C B δ₀:ℝ,∃M₀:ℕ,0<C ∧ 0<B ∧ 0<δ₀ ∧ δ₀ ≤ 1 ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g t L:ℕ,∀d:List ℕ,Stable g (d.length+1)→2 ≤ L→
    profileOrderWeight (M:ℝ) L (t::d)^2/(complexity g (d.length+1):ℝ)<δ₀→
    ∀Y∈Icc (0:ℝ) y₀,∀EC EG EP:ℕ→ℝ,
    (∀m,0 ≤ EC m)→(∀m,0 ≤ EG m)→(∀m,0 ≤ EP m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |cuspCorrection P g' p' Y-truncationValue (formalCusp P Y p') m (1/(complexity g' p':ℝ))| ≤
        EC m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |genusCorrection P g' p' Y-truncationValue (formalGenus P Y p') m (1/(complexity g' p':ℝ))| ≤
        EG m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    (∀g':ℕ,∀d':List ℕ,1 ≤ d'.length→Stable g' d'.length→∀m:ℕ,1 ≤ m→m<L→
      |profile P g' d' Y-truncationValue (formalProfile P Y d') m (1/(complexity g' d'.length:ℝ))| ≤
        EP m*profileOrderWeight (M:ℝ) m d'^(2*m)/(complexity g' d'.length:ℝ)^m)→
    |recursiveSeparatingWeightedLow P g t L d Y+recursiveSeparatingWeightedCentral P g t L d Y-
      truncationValue (separatingSeries P Y (formalHierarchyJet P Y) (L-1) t d) L (1/(complexity g (d.length+1):ℝ))| ≤
      C*profileOrderWeight (M:ℝ) L (t::d)^(2*L-1)/(complexity g (d.length+1):ℝ)^L*
        ((∑k∈Finset.range L,if 2 ≤ k then B^k*(EC (L-k)+EG (L-k)+EP (L-k)) else 0)+B^L) := by
  obtain ⟨Cl,Bl,M₀,hCl,hBl,hM₀,hlow⟩:=separating_low_uniform_remainder_step P
  obtain ⟨Cc,Bc,δ₀,hCc,hBc,hδ₀,hδ1,hcentral⟩:=separating_central_small_weight_uniform P
  let B:=max Bl Bc
  have hB:0<B:=hBl.trans_le (le_max_left _ _)
  refine ⟨Cl+Cc,B,δ₀,M₀,by positivity,hB,hδ₀,hδ1,hM₀,?_⟩
  intro M hM g t L d hstable hL hsmall Y hY EC EG EP hEC hEG hEP hcusp hgenus hprofile
  let S:=profileOrderWeight (M:ℝ) L (t::d)
  let h:ℝ:=complexity g (d.length+1)
  let E:ℝ:=((∑k∈Finset.range L,if 2 ≤ k then B^k*(EC (L-k)+EG (L-k)+EP (L-k)) else 0)+B^L)
  have hM2:(2:ℝ) ≤ M:=by exact_mod_cast hM₀.trans hM
  have hM0:0 ≤ (M:ℝ):=Nat.cast_nonneg _
  have hS0:0 ≤ S:=by dsimp[S,profileOrderWeight];positivity
  have hh:0<h:=by
    dsimp[h]
    have hn:0<complexity g (d.length+1):=by unfold complexity Stable at *;omega
    exact_mod_cast hn
  have hS:((d.length+1:ℕ):ℝ)+2*L ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hM2 (Nat.cast_nonneg L : (0:ℝ) ≤ L)
    dsimp[S,profileOrderWeight]
    simp only[List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith[Nat.cast_nonneg (α:=ℝ) (t::d).sum]
  have hsmall1:S^2/h<1:=hsmall.trans_le hδ1
  have hElow:(∑k∈Finset.range L,if 2 ≤ k then Bl^k*(EC (L-k)+EG (L-k)+EP (L-k)) else 0)+Bl^L ≤ E:=by
    apply add_le_add _ (pow_le_pow_left₀ hBl.le (le_max_left _ _) L)
    apply Finset.sum_le_sum
    intro k hk
    split_ifs
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hBl.le (le_max_left _ _) k)
        (add_nonneg (add_nonneg (hEC _) (hEG _)) (hEP _))
    · exact le_rfl
  have hEc:Bc^L ≤ E:=by
    apply LE.le.trans (pow_le_pow_left₀ hBc.le (le_max_right _ _) L)
    dsimp[E]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun k hk=>by
      split_ifs
      · exact mul_nonneg (pow_nonneg hB.le _) (add_nonneg (add_nonneg (hEC _) (hEG _)) (hEP _))
      · exact le_rfl))
  have hl:=hlow M hM g t L d hstable (by omega) hsmall1 Y hY EC EG EP hEC hEG hEP hcusp hgenus hprofile
  have hl':|recursiveSeparatingWeightedLow P g t L d Y-
      truncationValue (separatingSeries P Y (formalHierarchyJet P Y) (L-1) t d) L (1/h)| ≤ Cl*S^(2*L-1)/h^L*E:=by
    rw[recursiveSeparatingWeightedLow_error_eq_card P g t L d (by omega) Y hY S hstable hS hsmall1]
    exact hl.trans (mul_le_mul_of_nonneg_left hElow (by positivity:0 ≤ Cl*S^(2*L-1)/h^L))
  have hc:=hcentral (M:ℝ) hM2 g t L d hstable hL hsmall Y hY
  have hc':|recursiveSeparatingWeightedCentral P g t L d Y| ≤ Cc*S^(2*L-1)/h^L*E:=by
    apply hc.trans
    have ht:=mul_le_mul_of_nonneg_left hEc (by positivity:0 ≤ Cc*S^(2*L-1)/h^L)
    convert ht using 1 <;>ring
  have he:recursiveSeparatingWeightedLow P g t L d Y+recursiveSeparatingWeightedCentral P g t L d Y-
      truncationValue (separatingSeries P Y (formalHierarchyJet P Y) (L-1) t d) L (1/h)=
      (recursiveSeparatingWeightedLow P g t L d Y-
        truncationValue (separatingSeries P Y (formalHierarchyJet P Y) (L-1) t d) L (1/h))+
        recursiveSeparatingWeightedCentral P g t L d Y:=by ring
  rw[he]
  apply (abs_add_le _ _).trans ((add_le_add hl' hc').trans_eq _)
  ring

end WP.HigherOrder
