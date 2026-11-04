import WPFormalization.Analysis.SplittingSymmetry
import WPFormalization.Marked.FirstDegreeChildren
import WPFormalization.Marked.SeparatingRemainder

/-! Exact removal of both orientations of the two smallest separating components. The signed recursion remainder is bounded by the genuine all-zero cubic mass. -/

noncomputable section
open Set
namespace WP

def secondSeparatingTerm (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (u j : ℕ) (I : Finset ℕ) (Y : ℝ) : ℝ :=
  (4:ℝ)^g*normInt P j ((u:ℤ)::selected (d.map Int.ofNat) I) Y *
    normInt P (g-j) (((k:ℤ)-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length)\I)) Y /
      W P g (d.length+1) Y

lemma normInt_unstable_profile (P : PsiTheory) (g : ℕ) (d : List ℤ) (Y : ℝ)
    (hs : ¬Stable g d.length) : normInt P g d Y=0 := by
  unfold normInt
  split_ifs
  · exact normalized_unstable P g _ Y (by simpa only [List.length_map] using hs)
  · rfl

lemma secondSeparatingTerm_nonneg (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (u j : ℕ) (I : Finset ℕ) (hg : 2 ≤ g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    0 ≤ secondSeparatingTerm P g k d u j I Y := by
  unfold secondSeparatingTerm
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (normInt_nonneg_profile P _ _ (by simp) Y hY))
    (normInt_nonneg_profile P _ _ (by simp) Y hY))
      (W_pos P g _ (by omega) (by unfold Stable;omega) Y hY).le

lemma secondSeparatingTerm_unstable (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (u j : ℕ) (I : Finset ℕ) (hI : I⊆Finset.range d.length)
    (hloss : ¬(2 ≤ 2*j+I.card ∧ 2 ≤ 2*(g-j)+(d.length-I.card))) (Y : ℝ) :
    secondSeparatingTerm P g k d u j I Y=0 := by
  have hlen₁ := selected_length_card (d.map Int.ofNat) I (by simpa only [List.length_map] using hI)
  have hlen₂ := selected_length_card (d.map Int.ofNat) ((Finset.range d.length)\I)
    (by simpa only [List.length_map] using (Finset.sdiff_subset : Finset.range d.length\I⊆Finset.range d.length))
  rw [Finset.card_sdiff_of_subset hI,Finset.card_range] at hlen₂
  unfold secondSeparatingTerm
  by_cases hl : 2 ≤ 2*j+I.card
  · have hr : ¬Stable (g-j) (((k:ℤ)-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length)\I)).length := by
      simp only [List.length_cons,hlen₂,Stable]
      omega
    rw [normInt_unstable_profile P _ _ Y hr,mul_zero,zero_div]
  · have hr : ¬Stable j ((u:ℤ)::selected (d.map Int.ofNat) I).length := by
      simp only [List.length_cons,hlen₁,Stable]
      omega
    rw [normInt_unstable_profile P _ _ Y hr,mul_zero,zero_mul,zero_div]

lemma secondSeparatingTerm_reflect (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (u j : ℕ) (I : Finset ℕ) (hu : u∈Finset.range (k-1)) (hj : j ≤ g)
    (hI : I⊆Finset.range d.length) (Y : ℝ) :
    secondSeparatingTerm P g k d (k-2-u) (g-j) ((Finset.range d.length)\I) Y=
      secondSeparatingTerm P g k d u j I Y := by
  have hu' := Finset.mem_range.mp hu
  have h₁ : ((k-2-u:ℕ):ℤ)=(k:ℤ)-2-u := by omega
  have h₂ : (k:ℤ)-2-(k-2-u:ℕ)=u := by omega
  unfold secondSeparatingTerm
  rw [h₂,h₁,show g-(g-j)=j by omega,Finset.sdiff_sdiff_eq_self hI]
  ring

def secondSeparatingLeading (P : PsiTheory) (g k : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  ∑ u ∈ Finset.range (k-1),∑ j ∈ Finset.range (g+1),∑ I ∈ (Finset.range d.length).powerset,
    if 2*j+I.card=2 then secondSeparatingTerm P g k d u j I Y else 0

def secondSeparatingRemainder (P : PsiTheory) (g k : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  ∑ u ∈ Finset.range (k-1),∑ j ∈ Finset.range (g+1),∑ I ∈ (Finset.range d.length).powerset,
    if 3 ≤ 2*j+I.card ∧ 3 ≤ 2*(g-j)+(d.length-I.card) then
      secondSeparatingTerm P g k d u j I Y else 0

lemma secondSeparatingLeading_reflect (P : PsiTheory) (g k : ℕ) (d : List ℕ) (Y : ℝ) :
    secondSeparatingLeading P g k d Y=
      ∑ u ∈ Finset.range (k-1),∑ j ∈ Finset.range (g+1),∑ I ∈ (Finset.range d.length).powerset,
        if 2*(g-j)+(d.length-I.card)=2 then secondSeparatingTerm P g k d u j I Y else 0 := by
  unfold secondSeparatingLeading
  rw [Analysis.finite_splitting_sum_reflect k g (Finset.range d.length)]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro I hI
  have hIs := Finset.mem_powerset.mp hI
  rw [Finset.card_sdiff_of_subset hIs,Finset.card_range,
    secondSeparatingTerm_reflect P g k d u j I hu (by have := Finset.mem_range.mp hj;omega) hIs Y]

lemma secondSeparating_decomposition (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (hg : 3 ≤ g) (Y : ℝ) :
    (∑ u ∈ Finset.range (k-1),∑ j ∈ Finset.range (g+1),∑ I ∈ (Finset.range d.length).powerset,
      secondSeparatingTerm P g k d u j I Y)=
      2*secondSeparatingLeading P g k d Y+secondSeparatingRemainder P g k d Y := by
  have hpart : (∑ u ∈ Finset.range (k-1),∑ j ∈ Finset.range (g+1),∑ I ∈ (Finset.range d.length).powerset,
      secondSeparatingTerm P g k d u j I Y)=
      secondSeparatingLeading P g k d Y+
      (∑ u ∈ Finset.range (k-1),∑ j ∈ Finset.range (g+1),∑ I ∈ (Finset.range d.length).powerset,
        if 2*(g-j)+(d.length-I.card)=2 then secondSeparatingTerm P g k d u j I Y else 0)+
      secondSeparatingRemainder P g k d Y := by
    unfold secondSeparatingLeading secondSeparatingRemainder
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro I hI
    have hjg : j ≤ g := by have := Finset.mem_range.mp hj;omega
    have hIs := Finset.mem_powerset.mp hI
    have hcard : I.card ≤ d.length := by simpa only [Finset.card_range] using Finset.card_le_card hIs
    have hsum : (2*j+I.card)+(2*(g-j)+(d.length-I.card))=2*g+d.length := by omega
    by_cases hstable : 2 ≤ 2*j+I.card ∧ 2 ≤ 2*(g-j)+(d.length-I.card)
    · by_cases hl : 2*j+I.card=2
      · have hr : ¬2*(g-j)+(d.length-I.card)=2 := by omega
        have hm : ¬(3 ≤ 2*j+I.card ∧ 3 ≤ 2*(g-j)+(d.length-I.card)) := by omega
        simp [hl,hr,hm]
      · by_cases hr : 2*(g-j)+(d.length-I.card)=2
        · have hm : ¬(3 ≤ 2*j+I.card ∧ 3 ≤ 2*(g-j)+(d.length-I.card)) := by omega
          simp [hl,hr,hm]
        · have hm : 3 ≤ 2*j+I.card ∧ 3 ≤ 2*(g-j)+(d.length-I.card) := by omega
          simp [hl,hr,hm]
    · rw [secondSeparatingTerm_unstable P g k d u j I hIs hstable Y]
      simp
  rw [←secondSeparatingLeading_reflect P g k d Y] at hpart
  linarith
end WP

namespace WP
lemma secondSeparatingTerm_zero_majorant (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (u j : ℕ) (I : Finset ℕ) (hg : 2 ≤ g) (hj : j ≤ g)
    (hI : I⊆Finset.range d.length) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    secondSeparatingTerm P g k d u j I Y ≤
      W P j (I.card+1) Y*W P (g-j) (d.length-I.card+1) Y/W P g (d.length+1) Y := by
  have hlen₁ := selected_length_card (d.map Int.ofNat) I (by simpa only [List.length_map] using hI)
  have hlen₂ := selected_length_card (d.map Int.ofNat) ((Finset.range d.length)\I)
    (by simpa only [List.length_map] using (Finset.sdiff_subset : Finset.range d.length\I⊆Finset.range d.length))
  rw [Finset.card_sdiff_of_subset hI,Finset.card_range] at hlen₂
  have hleft := normInt_le_all_zero P j ((u:ℤ)::selected (d.map Int.ofNat) I) (by simp) Y hY
  have hright := normInt_le_all_zero P (g-j)
    (((k:ℤ)-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length)\I)) (by simp) Y hY
  simp only [List.length_cons,hlen₁,hlen₂] at hleft hright
  have hprod := mul_le_mul hleft hright
    (normInt_nonneg_profile P _ _ (by simp) Y hY)
    (normalized_nonneg_nonempty P _ _ (by simp) Y hY)
  have hpow : (4:ℝ)^j*(4:ℝ)^(g-j)=(4:ℝ)^g := by rw [←pow_add,Nat.add_sub_of_le hj]
  have he : (4:ℝ)^g*(normalized P j (List.replicate (I.card+1) 0) Y*
      normalized P (g-j) (List.replicate (d.length-I.card+1) 0) Y)=
      W P j (I.card+1) Y*W P (g-j) (d.length-I.card+1) Y := by
    unfold W
    rw [←hpow]
    ring
  unfold secondSeparatingTerm
  calc
    _ ≤ ((4:ℝ)^g*(normalized P j (List.replicate (I.card+1) 0) Y*
      normalized P (g-j) (List.replicate (d.length-I.card+1) 0) Y))/W P g (d.length+1) Y := by
        apply div_le_div_of_nonneg_right _ (W_pos P g _ (by omega) (by unfold Stable;omega) Y hY).le
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (show 0≤(4:ℝ)^g by positivity)
    _ = _ := by rw [he]

lemma secondSeparatingRemainder_le_zero (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    secondSeparatingRemainder P g k d Y ≤ ((k-1:ℕ):ℝ)*markedSplitRemainder P g (d.length+1) 1 Y := by
  have hpoint (u : ℕ) :
      (∑ j ∈ Finset.range (g+1),∑ I ∈ (Finset.range d.length).powerset,
        if 3 ≤ 2*j+I.card ∧ 3 ≤ 2*(g-j)+(d.length-I.card) then
          secondSeparatingTerm P g k d u j I Y else 0) ≤ markedSplitRemainder P g (d.length+1) 1 Y := by
    unfold markedSplitRemainder
    apply Finset.sum_le_sum
    intro j hj
    have hjg : j ≤ g := by have := Finset.mem_range.mp hj;omega
    calc
      _ ≤ ∑ I ∈ (Finset.range d.length).powerset,
          if 3 ≤ 2*j+I.card ∧ 3 ≤ 2*(g-j)+(d.length-I.card) then
            W P j (I.card+1) Y*W P (g-j) (d.length-I.card+1) Y/W P g (d.length+1) Y else 0 := by
        apply Finset.sum_le_sum
        intro I hI
        split_ifs
        · exact secondSeparatingTerm_zero_majorant P g k d u j I hg hjg (Finset.mem_powerset.mp hI) Y hY
        · exact le_rfl
      _ = markedSplitRemainderGenus P g (d.length+1) 1 j Y := by
        have he := Finset.sum_powerset_apply_card (fun s =>
          if 3 ≤ 2*j+s ∧ 3 ≤ 2*(g-j)+(d.length-s) then
            W P j (s+1) Y*W P (g-j) (d.length-s+1) Y/W P g (d.length+1) Y else 0)
          (x := Finset.range d.length)
        rw [he]
        simp only [Finset.card_range,nsmul_eq_mul]
        unfold markedSplitRemainderGenus
        simp only [Nat.add_sub_cancel]
        apply Finset.sum_congr rfl
        intro s hs
        have hs0 := Finset.mem_range.mp hs
        have hlen : d.length+1-s=d.length-s+1 := by omega
        split_ifs
        · unfold markedSplitTerm
          simp only [Nat.add_sub_cancel]
          rw [hlen]
          ring
        · ring
  calc
    _ ≤ ∑ u ∈ Finset.range (k-1), markedSplitRemainder P g (d.length+1) 1 Y :=
      Finset.sum_le_sum (fun u _ => hpoint u)
    _ = _ := by simp

lemma secondSeparatingRemainder_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ k : ℕ, ∀ d : List ℕ, d.length+1=p →
      ∀ Y ∈ Icc (0:ℝ) y₀,
      0 ≤ secondSeparatingRemainder P g k d Y ∧
        secondSeparatingRemainder P g k d Y ≤ C*((k:ℝ)+1)/(complexity g p:ℝ)^3 := by
  obtain ⟨C,hC,G,hbound⟩ := markedSplitRemainder_all_markings_bound P p hp
  refine ⟨C*((p:ℝ)+2)^3,by positivity,max G 2,?_⟩
  intro g hg k d hd Y hY
  have hgG : G ≤ g := (le_max_left _ _).trans hg
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hsize : (complexity g p:ℝ) ≤ ((p:ℝ)+2)*(g:ℝ) := by
    have hmul : p ≤ p*g := by simpa using Nat.mul_le_mul_left p (show 1≤g by omega)
    exact_mod_cast (calc complexity g p ≤ 2*g+p := by unfold complexity;omega
                        _ ≤ 2*g+p*g := by omega
                        _ = (p+2)*g := by ring)
  have hpow := pow_le_pow_left₀ hhp.le hsize 3
  have hbc : markedSplitRemainder P g p 1 Y ≤ C*((p:ℝ)+2)^3/(complexity g p:ℝ)^3 := by
    exact (hbound g hgG Y hY).trans ((div_le_div_iff₀ (pow_pos hgp _) (pow_pos hhp _)).2
      (by simpa only [mul_pow,mul_assoc] using mul_le_mul_of_nonneg_left hpow hC.le))
  constructor
  · apply Finset.sum_nonneg;intro u hu
    apply Finset.sum_nonneg;intro j hj
    apply Finset.sum_nonneg;intro I hI
    split_ifs
    · exact secondSeparatingTerm_nonneg P g k d u j I hg2 Y hY
    · exact le_rfl
  · calc
      _ ≤ ((k-1:ℕ):ℝ)*markedSplitRemainder P g (d.length+1) 1 Y :=
        secondSeparatingRemainder_le_zero P g k d hg2 Y hY
      _ = ((k-1:ℕ):ℝ)*markedSplitRemainder P g p 1 Y := by rw [hd]
      _ ≤ ((k-1:ℕ):ℝ)*(C*((p:ℝ)+2)^3/(complexity g p:ℝ)^3) :=
        mul_le_mul_of_nonneg_left hbc (Nat.cast_nonneg _)
      _ ≤ ((k:ℝ)+1)*(C*((p:ℝ)+2)^3/(complexity g p:ℝ)^3) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (show k-1 ≤ k+1 by omega)) (by positivity)
      _ = _ := by ring
end WP
