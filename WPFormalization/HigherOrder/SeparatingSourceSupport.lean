import WPFormalization.HigherOrder.SeparatingRemainderIdentity
/-! The actual low and central separating sources retain their original finite deficit prefix.
The finite original sums agree with the true absolutely summable formal pairing. -/

noncomputable section
namespace WP.HigherOrder
open Set
lemma separatingAtomValue_eq_secondSeparating_node_sum (P:PsiTheory) (g t j l:ℕ)
    (d:List ℕ) (I:Finset ℕ) (hj:j ≤ g) (hI:I⊆Finset.range d.length)
    (hlarge:Stable (g-j) (d.length+1-I.card)) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    separatingAtomValue P g t d Y j I l=
      ∑u∈Finset.range (t+l-1),secondSeparatingTerm P g (t+l) d u j I Y:=by
  have hcard:I.card<d.length+1:=by
    have hh:=Finset.card_le_card hI
    simp only[Finset.card_range] at hh
    omega
  unfold separatingAtomValue
  rw[large_component_ratio_exact_core P g (d.length+1) j I.card Y hY hj hcard hlarge,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw[recursiveSeparatingTerm_exact_core P g (t+l) j u d I hu hj hI hlarge Y hY]
  ring

lemma recursiveSeparatingTail_zero_beyond_deficit (P:PsiTheory) (g t L l:ℕ)
    (d:List ℕ) (hL:2 ≤ L) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀)
    (hl:deficit g (t::d)<l) :recursiveSeparatingTail P g (t+l) L d Y=0:=by
  unfold recursiveSeparatingTail
  rw[Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have hjg:j ≤ g:=by have h:=Finset.mem_range.mp hj;omega
  rw[Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro I hI
  have hIs:=Finset.mem_powerset.mp hI
  have hcard:I.card ≤ d.length:=by simpa only[Finset.card_range] using Finset.card_le_card hIs
  by_cases hc:L ≤ 2*j+I.card ∧ L ≤ 2*(g-j)+(d.length-I.card)
  · simp only[ite_eq_left hc]
    have hs:Stable j (I.card+1):=by unfold Stable;omega
    have ht:Stable (g-j) (d.length+1-I.card):=by unfold Stable;omega
    rw[←separatingAtomValue_eq_secondSeparating_node_sum P g t j l d I hjg hIs ht Y hY]
    exact separatingAtomValue_zero_beyond_deficit P g t j l d I hIs hjg hs ht Y hl
  · simp only[ite_eq_right hc,Finset.sum_const_zero]

lemma recursiveSeparatingTail_weighted_prefix_hasSum (P:PsiTheory) (g t L:ℕ)
    (d:List ℕ) (hL:2 ≤ L) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    HasSum (fun l:ℕ=>weight Y l*(recursiveSeparatingTail P g (t+l) L d Y/2))
      (∑l∈Finset.range (deficit g (t::d)+1),weight Y l*(recursiveSeparatingTail P g (t+l) L d Y/2)):=by
  apply hasSum_sum_of_ne_finset_zero
  intro l hl
  have hh:deficit g (t::d)<l:=by
    have h:¬l<deficit g (t::d)+1:=by simpa only[Finset.mem_range] using hl
    omega
  rw[recursiveSeparatingTail_zero_beyond_deficit P g t L l d hL Y hY hh,zero_div,mul_zero]

lemma recursiveSeparatingWeightedLow_finite_prefix (P:PsiTheory) (g t L:ℕ)
    (d:List ℕ) (hL:1 ≤ L) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) (S:ℝ)
    (hs:Stable g (d.length+1)) (hS:((d.length+1:ℕ):ℝ)+2*L ≤ S)
    (hsmall:S^2/(complexity g (d.length+1):ℝ)<1) :
    recursiveSeparatingWeightedLow P g t L d Y=
      ∑l∈Finset.range (deficit g (t::d)+1),weight Y l*recursiveSeparatingLow P g (t+l) L d Y:=by
  let N:=Finset.range (deficit g (t::d)+1)
  let J:=Finset.range L
  let D:=(Finset.range d.length).powerset
  let Q:ℕ→ℕ→Finset ℕ→ℝ:=fun l j I=>
    if Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ L-1 then
      weight Y l*separatingAtomValue P g t d Y j I l else 0
  have hcut:recursiveSeparatingWeightedLow P g t L d Y=∑j∈J,∑I∈D,∑l∈N,Q l j I:=by
    unfold recursiveSeparatingWeightedLow
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro I hI
    have hIs:=Finset.mem_powerset.mp hI
    have hcard:I.card<d.length+1:=by
      have hh:=Finset.card_le_card hIs
      simp only[Finset.card_range] at hh
      omega
    by_cases h:Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ L-1
    · simp only[Q,ite_eq_left h]
      obtain ⟨hjg,hlarge⟩:=small_weight_split_child_valid g (d.length+1) j I.card L S
        (by omega) hL hs hS hsmall (by omega) hcard
      exact (separating_atom_value_hasSum P g t j d I hIs hjg h.1 hlarge Y).tsum_eq
    · simp only[Q,ite_eq_right h,Finset.sum_const_zero]
  have hpoint (l:ℕ):(∑j∈J,∑I∈D,Q l j I)=weight Y l*recursiveSeparatingLow P g (t+l) L d Y:=by
    rw[recursiveSeparatingLow_exact_core P g (t+l) L d Y hY S hL hs hS hsmall]
    unfold recursiveSeparatingLowCore
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    have hIs:=Finset.mem_powerset.mp hI
    have hcard:I.card<d.length+1:=by
      have hh:=Finset.card_le_card hIs
      simp only[Finset.card_range] at hh
      omega
    by_cases h:Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ L-1
    · simp only[Q,ite_eq_left h]
      unfold separatingAtomValue
      rw[large_component_ratio_exact_core_small_weight P g (d.length+1) j I.card L Y hY S
        (by omega) hL hs hS hsmall (by omega) hcard]
    · simp only[Q,ite_eq_right h,mul_zero]
  calc
    _=∑j∈J,∑I∈D,∑l∈N,Q l j I:=hcut
    _=∑j∈J,∑l∈N,∑I∈D,Q l j I:=by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _=∑l∈N,∑j∈J,∑I∈D,Q l j I:=Finset.sum_comm
    _=∑l∈N,weight Y l*recursiveSeparatingLow P g (t+l) L d Y:=by
      apply Finset.sum_congr rfl
      intro l hl
      exact hpoint l
end WP.HigherOrder
