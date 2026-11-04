import WPFormalization.HigherOrder.SeparatingCoefficientSummability
set_option maxHeartbeats 800000
/-! Genuine separating coefficient sums and actual finite-deficit support.
Both component dimensions are used to prove exact tail vanishing.
The actual low source and the prescribed formal low jet have a true weighted remainder identity. -/

noncomputable section
namespace WP.HigherOrder
open Set
lemma separating_atom_coefficient_summable (P:PsiTheory) (t j n:ℕ) (d:List ℕ)
    (I:Finset ℕ) (hI:I⊆Finset.range d.length) (hst:Stable j (I.card+1))
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    Summable (fun l:ℕ=>weight Y l*PowerSeries.coeff n (separatingAtomSeries P Y t d j I l)):=by
  let a:=ratioSeries Y (formalHierarchyJet P Y) (d.length+1) j I.card
  let F:ℕ→Series:=fun l=>PowerSeries.C (weight Y l)*
    ∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P Y j (u::selectedNat d I))*
      complexityShift ((2*j+I.card:ℕ):ℝ)
        (formalProfile P Y ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))
  have hF:∀m:ℕ,Summable (fun l:ℕ=>PowerSeries.coeff m (F l)):=by
    intro m
    simpa only[F,PowerSeries.coeff_C_mul] using separating_inner_coefficient_summable P t j m d I hI hst Y hY
  have hs:=(coefficientSum_mul_left_hasSum a F hF n).summable
  convert hs using 1
  funext l
  have he:a*F l=PowerSeries.C (weight Y l)*separatingAtomSeries P Y t d j I l:=by
    dsimp[a,F,separatingAtomSeries]
    ring
  rw[he,PowerSeries.coeff_C_mul]

lemma separatingSeries_eq_guarded_atom_sum (P:PsiTheory) (t K:ℕ) (d:List ℕ)
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    separatingSeries P Y (formalHierarchyJet P Y) K t d=
      ∑j∈Finset.range (K+1),∑I∈(Finset.range d.length).powerset,
        if Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ K then
          coefficientSum (fun l=>PowerSeries.C (weight Y l)*separatingAtomSeries P Y t d j I l)
        else 0:=by
  unfold separatingSeries
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs with h
  · let a:=ratioSeries Y (formalHierarchyJet P Y) (d.length+1) j I.card
    let F:ℕ→Series:=fun l=>PowerSeries.C (weight Y l)*
      ∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P Y j (u::selectedNat d I))*
        complexityShift (2*(j:ℝ)+I.card)
          (formalProfile P Y ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))
    have hF:∀m:ℕ,Summable (fun l:ℕ=>PowerSeries.coeff m (F l)):=by
      intro m
      simpa only[F,PowerSeries.coeff_C_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using separating_inner_coefficient_summable P t j m d I
        (Finset.mem_powerset.mp hI) h.1 Y hY
    simp only[formalHierarchyJet]
    change a*coefficientSum F=_
    rw[←coefficientSum_mul_left a F hF]
    apply congrArg coefficientSum
    funext l
    dsimp[a,F,separatingAtomSeries]
    simp only[Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  · rfl

lemma selectedNat_partition_sum (d:List ℕ) (I:Finset ℕ) :
    (selectedNat d I).sum+(selectedNat d ((Finset.range d.length)\I)).sum=d.sum:=by
  have hp:=(selected_partition_perm (d.map Int.ofNat) I).map Int.toNat
  simp only[List.length_map,List.map_append,selectedNat_toNat,List.map_map,
    Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id'] at hp
  simpa only[List.sum_append] using hp.sum_eq

lemma separatingAtomValue_zero_beyond_deficit (P:PsiTheory) (g t j l:ℕ)
    (d:List ℕ) (I:Finset ℕ) (hI:I⊆Finset.range d.length) (hj:j ≤ g)
    (hsmall:Stable j (I.card+1)) (hlarge:Stable (g-j) (d.length+1-I.card))
    (Y:ℝ) (hl:deficit g (t::d)<l) :
    separatingAtomValue P g t d Y j I l=0:=by
  have hcard:I.card ≤ d.length:=by simpa only[Finset.card_range] using Finset.card_le_card hI
  have hcomp:(Finset.range d.length)\I⊆Finset.range d.length:=Finset.sdiff_subset
  have hlen₁:(selectedNat d I).length=I.card:=separating_selected_length d I hI
  have hlen₂:(selectedNat d ((Finset.range d.length)\I)).length=d.length-I.card:=by
    rw[separating_selected_length d _ hcomp,Finset.card_sdiff_of_subset hI,Finset.card_range]
  have hdim:dimension j (I.card+1)+dimension (g-j) (d.length+1-I.card)+2=dimension g (d.length+1):=by
    unfold dimension Stable at *
    omega
  have hpart:=selectedNat_partition_sum d I
  have hlargeD:dimension g (d.length+1)<(t::d).sum+l:=by
    unfold deficit at hl
    simp only[List.length_cons] at hl
    omega
  unfold separatingAtomValue
  have hs:(∑u∈Finset.range (t+l-1),smallW P Y j (u::selectedNat d I)*
      profile P (g-j) ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)) Y)=0:=by
    apply Finset.sum_eq_zero
    intro u hu
    have hu':u<t+l-1:=Finset.mem_range.mp hu
    by_cases he:dimension j (u::selectedNat d I).length<(u::selectedNat d I).sum
    · rw[smallW,normalized_excess P j _ Y he,mul_zero,zero_mul]
    · have hx:dimension (g-j) ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)).length<
          ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)).sum:=by
        simp only[List.length_cons,hlen₁,hlen₂,List.sum_cons] at he ⊢
        have hh:d.length-I.card+1=d.length+1-I.card:=by omega
        rw[hh]
        simp only[List.sum_cons] at hlargeD
        omega
      rw[profile_excess_zero P (g-j) _ Y hx,mul_zero]
  rw[hs,mul_zero]

lemma separating_atom_value_hasSum (P:PsiTheory) (g t j:ℕ)
    (d:List ℕ) (I:Finset ℕ) (hI:I⊆Finset.range d.length) (hj:j ≤ g)
    (hsmall:Stable j (I.card+1)) (hlarge:Stable (g-j) (d.length+1-I.card)) (Y:ℝ) :
    HasSum (fun l:ℕ=>weight Y l*separatingAtomValue P g t d Y j I l)
      (∑l∈Finset.range (deficit g (t::d)+1),weight Y l*separatingAtomValue P g t d Y j I l):=by
  apply hasSum_sum_of_ne_finset_zero
  intro l hl
  have hlt:deficit g (t::d)<l:=by
    have hh:¬l<deficit g (t::d)+1:=by simpa only[Finset.mem_range] using hl
    omega
  rw[separatingAtomValue_zero_beyond_deficit P g t j l d I hI hj hsmall hlarge Y hlt,mul_zero]

lemma separating_atom_remainder_hasSum (P:PsiTheory) (g t j L:ℕ)
    (d:List ℕ) (I:Finset ℕ) (hI:I⊆Finset.range d.length) (hj:j ≤ g)
    (hsmall:Stable j (I.card+1)) (hlarge:Stable (g-j) (d.length+1-I.card))
    (Y z:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    HasSum (fun l:ℕ=>weight Y l*(separatingAtomValue P g t d Y j I l-
      truncationValue (separatingAtomSeries P Y t d j I l) L z))
      ((∑'l:ℕ,weight Y l*separatingAtomValue P g t d Y j I l)-
        truncationValue (coefficientSum (fun l=>PowerSeries.C (weight Y l)*
          separatingAtomSeries P Y t d j I l)) L z):=by
  exact weighted_operator_remainder_hasSum (weight Y) (separatingAtomValue P g t d Y j I)
    (separatingAtomSeries P Y t d j I) L z _
    (separating_atom_value_hasSum P g t j d I hI hj hsmall hlarge Y).summable.hasSum
    (fun n hn=>separating_atom_coefficient_summable P t j n d I hI hsmall Y hY)

def recursiveSeparatingWeightedLow (P:PsiTheory) (g t L:ℕ) (d:List ℕ) (Y:ℝ):ℝ :=
  ∑j∈Finset.range L,∑I∈(Finset.range d.length).powerset,
    if Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ L-1 then
      ∑'l:ℕ,weight Y l*separatingAtomValue P g t d Y j I l else 0

lemma recursiveSeparatingWeightedLow_remainder_identity (P:PsiTheory) (g t L:ℕ)
    (d:List ℕ) (hL:1 ≤ L) (Y z:ℝ) (hY:Y∈Icc (0:ℝ) y₀) (S:ℝ)
    (hs:Stable g (d.length+1)) (hS:((d.length+1:ℕ):ℝ)+2*L ≤ S)
    (hsmall:S^2/(complexity g (d.length+1):ℝ)<1) :
    recursiveSeparatingWeightedLow P g t L d Y-
      truncationValue (separatingSeries P Y (formalHierarchyJet P Y) (L-1) t d) L z=
        ∑j∈Finset.range L,∑I∈(Finset.range d.length).powerset,
          if Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ L-1 then
            ∑'l:ℕ,weight Y l*(separatingAtomValue P g t d Y j I l-
              truncationValue (separatingAtomSeries P Y t d j I l) L z) else 0:=by
  have hformal:truncationValue (separatingSeries P Y (formalHierarchyJet P Y) (L-1) t d) L z=
      ∑j∈Finset.range L,∑I∈(Finset.range d.length).powerset,
        if Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ L-1 then
          truncationValue (coefficientSum (fun l=>PowerSeries.C (weight Y l)*
            separatingAtomSeries P Y t d j I l)) L z else 0:=by
    rw[separatingSeries_eq_guarded_atom_sum P t (L-1) d Y hY,
      Nat.sub_add_cancel hL,truncationValue_finset_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw[truncationValue_finset_sum]
    apply Finset.sum_congr rfl
    intro I hI
    split_ifs
    · rfl
    · simp only[truncationValue,map_zero,zero_mul,Finset.sum_const_zero]
  rw[hformal]
  simp only[recursiveSeparatingWeightedLow,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs with h
  · have hIs:=Finset.mem_powerset.mp hI
    have hcard:I.card<d.length+1:=by
      have hh:=Finset.card_le_card hIs
      simp only[Finset.card_range] at hh
      omega
    obtain ⟨hjg,hlarge⟩:=small_weight_split_child_valid g (d.length+1) j I.card L S
      (by omega) hL hs hS hsmall (by omega) hcard
    exact (separating_atom_remainder_hasSum P g t j L d I hIs hjg h.1 hlarge Y z hY).tsum_eq.symm
  · ring

end WP.HigherOrder
