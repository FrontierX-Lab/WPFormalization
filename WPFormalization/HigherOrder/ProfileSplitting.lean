import WPFormalization.Marked.SecondSeparatingDecomposition
import WPFormalization.Marked.TopologyTailDefinitions
import WPFormalization.HigherOrder.ActualRatioProduct
import WPFormalization.HigherOrder.OrderWeights
/-! The genuine profile separating sum is partitioned into one orientation of
all low-loss components and a central double-loss tail. Reflection preserves
the signed original node degrees, and unstable terms remain zero. The tail
is bounded by the original all-zero C.5 mass; each retained actual term is
factored into the true bounded component, large profile, and exact C.14 core.
No separating remainder estimate is assumed by these identities. -/
noncomputable section
namespace WP.HigherOrder
open Set

def recursiveSeparatingLow (P:PsiTheory)(g k L:ℕ)(d:List ℕ)(Y:ℝ):ℝ :=
  ∑u∈Finset.range (k-1),∑j∈Finset.range (g+1),∑I∈(Finset.range d.length).powerset,
    if 2≤2*j+I.card ∧ 2*j+I.card<L then secondSeparatingTerm P g k d u j I Y else 0

def recursiveSeparatingTail (P:PsiTheory)(g k L:ℕ)(d:List ℕ)(Y:ℝ):ℝ :=
  ∑u∈Finset.range (k-1),∑j∈Finset.range (g+1),∑I∈(Finset.range d.length).powerset,
    if L≤2*j+I.card ∧ L≤2*(g-j)+(d.length-I.card) then secondSeparatingTerm P g k d u j I Y else 0

lemma recursiveSeparatingLow_reflect (P:PsiTheory)(g k L:ℕ)(d:List ℕ)(Y:ℝ) :
    recursiveSeparatingLow P g k L d Y=
      ∑u∈Finset.range (k-1),∑j∈Finset.range (g+1),∑I∈(Finset.range d.length).powerset,
        if 2≤2*(g-j)+(d.length-I.card) ∧ 2*(g-j)+(d.length-I.card)<L then
          secondSeparatingTerm P g k d u j I Y else 0 := by
  unfold recursiveSeparatingLow
  rw [Analysis.finite_splitting_sum_reflect k g (Finset.range d.length)]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro I hI
  have hIs:=Finset.mem_powerset.mp hI
  rw [Finset.card_sdiff_of_subset hIs,Finset.card_range,
    secondSeparatingTerm_reflect P g k d u j I hu (by have :=Finset.mem_range.mp hj;omega) hIs Y]

lemma recursiveSeparating_orientation_decomposition (P:PsiTheory)(g k L:ℕ)(d:List ℕ)
    (hsep:2*L≤2*g+d.length)(Y:ℝ) :
    (1/2:ℝ)*(∑u∈Finset.range (k-1),∑j∈Finset.range (g+1),∑I∈(Finset.range d.length).powerset,
      secondSeparatingTerm P g k d u j I Y)=
        recursiveSeparatingLow P g k L d Y+(1/2:ℝ)*recursiveSeparatingTail P g k L d Y := by
  have hpart:(∑u∈Finset.range (k-1),∑j∈Finset.range (g+1),∑I∈(Finset.range d.length).powerset,
      secondSeparatingTerm P g k d u j I Y)=
        recursiveSeparatingLow P g k L d Y+
        (∑u∈Finset.range (k-1),∑j∈Finset.range (g+1),∑I∈(Finset.range d.length).powerset,
          if 2≤2*(g-j)+(d.length-I.card) ∧ 2*(g-j)+(d.length-I.card)<L then
            secondSeparatingTerm P g k d u j I Y else 0)+recursiveSeparatingTail P g k L d Y := by
    unfold recursiveSeparatingLow recursiveSeparatingTail
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro I hI
    have hjg:j≤g := by have :=Finset.mem_range.mp hj;omega
    have hIs:=Finset.mem_powerset.mp hI
    have hcard:I.card≤d.length := by simpa only [Finset.card_range] using Finset.card_le_card hIs
    have hsum:(2*j+I.card)+(2*(g-j)+(d.length-I.card))=2*g+d.length := by omega
    by_cases hstable:2≤2*j+I.card ∧ 2≤2*(g-j)+(d.length-I.card)
    · by_cases hleft:2*j+I.card<L
      · have hright:¬2*(g-j)+(d.length-I.card)<L := by omega
        have htail:¬(L≤2*j+I.card ∧ L≤2*(g-j)+(d.length-I.card)) := by omega
        simp only [hstable.1,hstable.2,hleft,hright,htail,and_self,and_true,and_false,ite_true,ite_false,add_zero]
      · by_cases hright:2*(g-j)+(d.length-I.card)<L
        · have htail:¬(L≤2*j+I.card ∧ L≤2*(g-j)+(d.length-I.card)) := by omega
          simp only [hstable.1,hstable.2,hleft,hright,htail,and_self,and_true,and_false,ite_true,ite_false,zero_add,add_zero]
        · have htail:L≤2*j+I.card ∧ L≤2*(g-j)+(d.length-I.card) := by omega
          simp only [hstable.1,hstable.2,hleft,hright,htail,and_self,and_true,and_false,ite_true,ite_false,zero_add]
    · rw [secondSeparatingTerm_unstable P g k d u j I hIs hstable Y]
      simp
  rw [←recursiveSeparatingLow_reflect P g k L d Y] at hpart
  linarith

lemma recursiveSeparatingTail_nonneg (P:PsiTheory)(g k L:ℕ)(d:List ℕ)(hg:2≤g)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀) : 0≤recursiveSeparatingTail P g k L d Y := by
  unfold recursiveSeparatingTail
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro I hI
  split_ifs
  · exact secondSeparatingTerm_nonneg P g k d u j I hg Y hY
  · exact le_rfl

lemma recursiveSeparatingTail_le_zero (P:PsiTheory)(g k L:ℕ)(d:List ℕ)(hg:2≤g)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀) :
    recursiveSeparatingTail P g k L d Y≤
      ((k-1:ℕ):ℝ)*markedSplitLossTail P g (d.length+1) 1 L Y := by
  have hpoint (u:ℕ):
      (∑j∈Finset.range (g+1),∑I∈(Finset.range d.length).powerset,
        if L≤2*j+I.card ∧ L≤2*(g-j)+(d.length-I.card) then
          secondSeparatingTerm P g k d u j I Y else 0)≤
        markedSplitLossTail P g (d.length+1) 1 L Y := by
    unfold markedSplitLossTail
    apply Finset.sum_le_sum
    intro j hj
    have hjg:j≤g := by have :=Finset.mem_range.mp hj;omega
    calc
      _≤∑I∈(Finset.range d.length).powerset,
          if L≤2*j+I.card ∧ L≤2*(g-j)+(d.length-I.card) then
            W P j (I.card+1) Y*W P (g-j) (d.length-I.card+1) Y/W P g (d.length+1) Y else 0 := by
        apply Finset.sum_le_sum
        intro I hI
        split_ifs
        · exact secondSeparatingTerm_zero_majorant P g k d u j I hg hjg (Finset.mem_powerset.mp hI) Y hY
        · exact le_rfl
      _=markedSplitLossTailGenus P g (d.length+1) 1 L j Y := by
        have he:=Finset.sum_powerset_apply_card (fun s=>
          if L≤2*j+s ∧ L≤2*(g-j)+(d.length-s) then
            W P j (s+1) Y*W P (g-j) (d.length-s+1) Y/W P g (d.length+1) Y else 0)
          (x:=Finset.range d.length)
        rw [he]
        simp only [Finset.card_range,nsmul_eq_mul]
        unfold markedSplitLossTailGenus
        simp only [Nat.add_sub_cancel]
        apply Finset.sum_congr rfl
        intro s hs
        have hs0:=Finset.mem_range.mp hs
        have hlen:d.length+1-s=d.length-s+1 := by omega
        split_ifs
        · unfold markedSplitTerm
          simp only [Nat.add_sub_cancel]
          rw [hlen]
          ring
        · ring
  unfold recursiveSeparatingTail
  calc
    _≤∑u∈Finset.range (k-1),markedSplitLossTail P g (d.length+1) 1 L Y :=
      Finset.sum_le_sum (fun u _=>hpoint u)
    _=_ := by simp

lemma recursiveSeparatingTerm_exact_core (P:PsiTheory)(g k j u:ℕ)(d:List ℕ)(I:Finset ℕ)
    (hu:u∈Finset.range (k-1))(hj:j≤g)(hI:I⊆Finset.range d.length)
    (hstable:Stable (g-j) (d.length+1-I.card))
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀) :
    secondSeparatingTerm P g k d u j I Y=
      smallW P Y j (u::selectedNat d I)*
        profile P (g-j) ((k-2-u)::selectedNat d ((Finset.range d.length)\I)) Y*
        ((A Y/(complexity g (d.length+1):ℝ))^(2*j+I.card)*
          actualLargeRatioCore P g (d.length+1) j I.card Y) := by
  have hn (a b:ℕ)(J:Finset ℕ):
      normInt P a ((b:ℤ)::selected (d.map Int.ofNat) J) Y=
        normalized P a (b::selectedNat d J) Y := by
    have hnon:∀z∈((b:ℤ)::selected (d.map Int.ofNat) J),0≤z := by
      intro z hz
      rcases List.mem_cons.mp hz with rfl|hz
      · positivity
      · exact selected_nat_nonneg d J z hz
    unfold normInt
    rw [if_pos hnon]
    simp only [List.map_cons,Int.toNat_natCast,selectedNat_toNat]
  have hcast:((k-2-u:ℕ):ℤ)=(k:ℤ)-2-u := by have :=Finset.mem_range.mp hu;omega
  have hc:I.card≤d.length := by simpa only [Finset.card_range] using Finset.card_le_card hI
  have hcomp:(Finset.range d.length)\I⊆Finset.range d.length := Finset.sdiff_subset
  have hlen:((k-2-u)::selectedNat d ((Finset.range d.length)\I)).length=d.length+1-I.card := by
    rw [List.length_cons,←selectedNat_toNat,List.length_map,
      selected_length_card _ _ (by simpa only [List.length_map] using hcomp),
      Finset.card_sdiff_of_subset hI,Finset.card_range]
    omega
  unfold secondSeparatingTerm
  rw [hn,←hcast,hn]
  exact actual_split_large_component_factor P g (d.length+1) j I.card _ _ hlen Y hY hj (by omega) hstable

end WP.HigherOrder
