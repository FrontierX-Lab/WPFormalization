import WPFormalization.Weighted.ComplexityReindex
import WPFormalization.Weighted.LabelFilter
import WPFormalization.Weighted.SeparatingSeries
import WPFormalization.Weighted.GammaEnvelope
import WPFormalization.Weighted.ActiveDimension

/-! Complete oriented Gamma/label envelope, for every stable complexity. Small complexities are bounded on an explicitly finite parameter set. -/
noncomputable section
namespace WP
def partitionLabelProfile {α : Type*} [DecidableEq α] (A : Finset α) (N k i : ℕ) (U : Finset α) : ℝ :=
  if i≠0 ∨ 2≤(U∩A).card then
    ((U.card : ℝ)+2)/(N.choose k : ℝ)*Real.exp ((k+1 : ℕ)/12)/Real.sqrt (A.card.choose (U∩A).card)
  else 0
lemma partitionLabelProfile_nonneg {α : Type*} [DecidableEq α] (A : Finset α) (N k i : ℕ) (U : Finset α) :
    0 ≤ partitionLabelProfile A N k i U := by
  unfold partitionLabelProfile
  split_ifs <;> positivity
lemma partitionLabelProfile_layer {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (N k i : ℕ) :
    (∑ U ∈ (A∪B).powerset, if U.card=k+2-2*i then partitionLabelProfile A N k i U else 0) =
      separatingSeriesTerm A.card B.card N k i := by
  let s := k+2-2*i
  let T : ℝ := ((s : ℝ)+2)/(N.choose k : ℝ)*Real.exp ((k+1 : ℕ)/12)
  have he : (∑ U ∈ (A∪B).powerset, if U.card=s then partitionLabelProfile A N k i U else 0) =
      T*(∑ U ∈ (A∪B).powerset, if U.card=s ∧ (i≠0 ∨ 2≤(U∩A).card) then
        1/Real.sqrt (A.card.choose (U∩A).card) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    unfold partitionLabelProfile
    by_cases hs : U.card=s <;> by_cases hq : i≠0 ∨ 2≤(U∩A).card <;>
      simp only [hs,hq,true_and,false_and,ite_true,ite_false,mul_zero]
    dsimp only [T]
    ring
  rw [he,powerset_filtered_label_envelope A B hAB s (fun u => i≠0 ∨ 2≤u)]
  by_cases hi : i=0
  · subst i
    simp only [ne_eq,not_true_eq_false,false_or,separatingSeriesTerm,separatingLabelEnvelope,ite_true,
      Nat.mul_zero,Nat.sub_zero]
    dsimp only [T,s]
    simp only [Nat.mul_zero,Nat.sub_zero,Nat.cast_add,Nat.cast_ofNat]
    ring
  · simp only [hi,ne_eq,not_false_eq_true,true_or,ite_true]
    unfold separatingSeriesTerm separatingLabelEnvelope
    rw [if_neg hi]
    change T*weightedLabelSum A.card B.card s =
      ((s : ℝ)+2)*weightedLabelSum A.card B.card s/(N.choose k : ℝ)*Real.exp ((k+1 : ℕ)/12)
    dsimp only [T]
    push_cast
    ring
lemma partitionLabelProfile_total : ∃ C : ℝ, 0<C ∧ ∀ {α : Type*} [DecidableEq α],
    ∀ A B : Finset α, Disjoint A B → ∀ g N : ℕ, A.card+B.card≤N → 3*B.card≤2*N →
    (∑ i ∈ Finset.range (g+1), ∑ U ∈ (A∪B).powerset,
      if 2≤2*i+U.card ∧ 2*(2*i+U.card-2)≤N then
        partitionLabelProfile A N (2*i+U.card-2) i U else 0) ≤ C*(1+(A.card : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := separatingSeries_total_bound
  refine ⟨C,hC,?_⟩
  intro α inst A B hAB g N hsize hR
  calc
    _ ≤ ∑ k ∈ Finset.range (N/2+1), ∑ i ∈ Finset.range (k+3), ∑ U ∈ (A∪B).powerset,
        if U.card=k+2-2*i then partitionLabelProfile A N k i U else 0 :=
      sum_complexity_reindex_nested (A∪B).powerset Finset.card g N
        (fun k i U => partitionLabelProfile A N k i U) (partitionLabelProfile_nonneg A N)
    _ = ∑ k ∈ Finset.range (N/2+1), ∑ i ∈ Finset.range (k+3), separatingSeriesTerm A.card B.card N k i := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      exact partitionLabelProfile_layer A B hAB N k i
    _ ≤ _ := hbound A.card B.card N hsize hR
def partitionGammaTerm {α : Type*} [DecidableEq α]
    (A : Finset α) (g n i : ℕ) (U : Finset α) : ℝ :=
  let h₁ := 2*i+U.card-1
  let h₂ := 2*(g-i)+(n-U.card)-1
  let h := 2*g+n-1
  if 1≤h₁ ∧ 1≤h₂ ∧ h₁≤h₂ ∧ (i≠0 ∨ 2≤(U∩A).card) then
    (Real.Gamma h₁*Real.Gamma h₂/Real.Gamma h)*
      (((U.card : ℝ)+2)*Real.sqrt h/Real.sqrt (A.card.choose (U∩A).card))*Real.exp ((h₁ : ℝ)/12)
  else 0
lemma gamma_label_factorization (h h₁ h₂ I u s : ℕ)
    (hh₁ : 1≤h₁) (hh₂ : 1≤h₂) (hsum : h₁+h₂+1=h) :
    (Real.Gamma h₁*Real.Gamma h₂/Real.Gamma h)*
      (((s : ℝ)+2)*Real.sqrt h/Real.sqrt (I.choose u))*Real.exp ((h₁ : ℝ)/12) =
    (Real.sqrt h/(((h : ℝ)-1)*((h : ℝ)-2)))*
      (((s : ℝ)+2)/((h-3).choose (h₁-1) : ℝ)*Real.exp ((h₁-1+1 : ℕ)/12)/Real.sqrt (I.choose u)) := by
  rw [gamma_split_binomial_complexity h h₁ h₂ hh₁ hh₂ hsum,show h₁-1+1=h₁ by omega]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring
lemma partitionGammaTerm_profile {α : Type*} [DecidableEq α]
    (A : Finset α) (g n i : ℕ) (U : Finset α) (hg : 2≤g) (hi : i≤g) (hs : U.card≤n) :
    partitionGammaTerm A g n i U ≤
      (Real.sqrt (2*g+n-1 : ℕ)/((((2*g+n-1 : ℕ) : ℝ)-1)*(((2*g+n-1 : ℕ) : ℝ)-2)))*
        (if 2≤2*i+U.card ∧ 2*(2*i+U.card-2)≤(2*g+n-1)-3 then
          partitionLabelProfile A ((2*g+n-1)-3) (2*i+U.card-2) i U else 0) := by
  let h₁ := 2*i+U.card-1
  let h₂ := 2*(g-i)+(n-U.card)-1
  let h := 2*g+n-1
  have hh : 3≤h := by dsimp only [h]; omega
  have hhR : (3 : ℝ)≤h := by exact_mod_cast hh
  have hCommon : 0≤Real.sqrt h/(((h : ℝ)-1)*((h : ℝ)-2)) :=
    div_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by linarith) (by linarith))
  unfold partitionGammaTerm
  dsimp only
  by_cases hv : 1≤h₁ ∧ 1≤h₂ ∧ h₁≤h₂ ∧ (i≠0 ∨ 2≤(U∩A).card)
  · rw [if_pos hv]
    have hsum : h₁+h₂+1=h := by dsimp only [h₁,h₂,h] at *; omega
    have hcond : 2≤2*i+U.card ∧ 2*(2*i+U.card-2)≤h-3 := by
      dsimp only [h₁,h₂,h] at *
      omega
    rw [if_pos hcond]
    unfold partitionLabelProfile
    rw [if_pos hv.2.2.2]
    have hk : h₁-1=2*i+U.card-2 := by dsimp only [h₁]; omega
    simpa only [hk] using
      (gamma_label_factorization h h₁ h₂ A.card (U∩A).card U.card hv.1 hv.2.1 hsum).le
  · rw [if_neg hv]
    apply mul_nonneg hCommon
    split_ifs
    · exact partitionLabelProfile_nonneg A _ _ _ _
    · exact le_rfl
lemma partitionGamma_total : ∃ C : ℝ, 0<C ∧ ∀ {α : Type*} [DecidableEq α],
    ∀ A B : Finset α, Disjoint A B → ∀ g : ℕ, 2≤g →
    3*B.card≤2*((2*g+(A∪B).card-1)-3) →
    (∑ i ∈ Finset.range (g+1), ∑ U ∈ (A∪B).powerset,
      partitionGammaTerm A g (A∪B).card i U) ≤
        C*(1+(A.card : ℝ))/Real.rpow (2*g+(A∪B).card-1 : ℕ) (3/2 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := partitionLabelProfile_total
  refine ⟨9*C,by positivity,?_⟩
  intro α inst A B hAB g hg hR
  let n := (A∪B).card
  let h := 2*g+n-1
  let N := h-3
  have hh : 3≤h := by dsimp only [h]; omega
  have hhR : (3 : ℝ)≤h := by exact_mod_cast hh
  have hsize : A.card+B.card≤N := by
    have hc := Finset.card_union_of_disjoint hAB
    dsimp only [N,h,n]
    omega
  have hCmn : 0≤Real.sqrt h/(((h : ℝ)-1)*((h : ℝ)-2)) :=
    div_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by linarith) (by linarith))
  calc
    _ ≤ ∑ i ∈ Finset.range (g+1), ∑ U ∈ (A∪B).powerset,
        (Real.sqrt h/(((h : ℝ)-1)*((h : ℝ)-2)))*
          (if 2≤2*i+U.card ∧ 2*(2*i+U.card-2)≤N then
            partitionLabelProfile A N (2*i+U.card-2) i U else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro U hU
      exact partitionGammaTerm_profile A g n i U hg (by have := Finset.mem_range.mp hi; omega)
        (Finset.card_le_card (Finset.mem_powerset.mp hU))
    _ = (Real.sqrt h/(((h : ℝ)-1)*((h : ℝ)-2)))*
        (∑ i ∈ Finset.range (g+1), ∑ U ∈ (A∪B).powerset,
          if 2≤2*i+U.card ∧ 2*(2*i+U.card-2)≤N then
            partitionLabelProfile A N (2*i+U.card-2) i U else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ ≤ (Real.sqrt h/(((h : ℝ)-1)*((h : ℝ)-2)))*(C*(1+(A.card : ℝ))) :=
      mul_le_mul_of_nonneg_left (hbound A B hAB g N hsize hR) hCmn
    _ ≤ (9/Real.rpow h (3/2 : ℝ))*(C*(1+(A.card : ℝ))) :=
      mul_le_mul_of_nonneg_right (gamma_denominator_sqrt h hhR) (by positivity)
    _ = _ := by ring
def partitionGammaCounts (g n I i u j : ℕ) : ℝ :=
  let h₁ := 2*i+(u+j)-1
  let h₂ := 2*(g-i)+(n-(u+j))-1
  let h := 2*g+n-1
  if 1≤h₁ ∧ 1≤h₂ ∧ h₁≤h₂ ∧ (i≠0 ∨ 2≤u) then
    (Real.Gamma h₁*Real.Gamma h₂/Real.Gamma h)*
      ((((u+j : ℕ) : ℝ)+2)*Real.sqrt h/Real.sqrt (I.choose u))*Real.exp ((h₁ : ℝ)/12)
  else 0
lemma partitionGammaCounts_nonneg (g n I i u j : ℕ) :
    0≤partitionGammaCounts g n I i u j := by
  unfold partitionGammaCounts
  dsimp only
  split_ifs
  · have h₁ := gamma_nat_nonneg (2*i+(u+j)-1)
    have h₂ := gamma_nat_nonneg (2*(g-i)+(n-(u+j))-1)
    have h := gamma_nat_nonneg (2*g+n-1)
    positivity
  · exact le_rfl
def smallGammaSum (I R g : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (g+1), ∑ u ∈ Finset.range (I+1), ∑ j ∈ Finset.range (R+1),
    (I.choose u : ℝ)*(R.choose j : ℝ)*partitionGammaCounts g (I+R) I i u j
lemma smallGammaSum_nonneg (I R g : ℕ) : 0 ≤ smallGammaSum I R g := by
  unfold smallGammaSum
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (partitionGammaCounts_nonneg g (I+R) I i u j)
lemma partitionGamma_sum_counts {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (g : ℕ) :
    (∑ i ∈ Finset.range (g+1), ∑ U ∈ (A∪B).powerset,
      partitionGammaTerm A g (A∪B).card i U) = smallGammaSum A.card B.card g := by
  unfold smallGammaSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sum_powerset_two_colors_choose A B hAB
    (fun u j => partitionGammaCounts g (A.card+B.card) A.card i u j)]
  apply Finset.sum_congr rfl
  intro U hU
  have hcard := card_two_color_split A B U hAB (Finset.mem_powerset.mp hU)
  have htotal := Finset.card_union_of_disjoint hAB
  unfold partitionGammaTerm partitionGammaCounts
  rw [htotal,hcard]
lemma smallGammaSum_uniform : ∃ C : ℝ, 0<C ∧ ∀ g I R : ℕ,
    g<30 → I<30 → R<30 →
    Real.rpow (2*g+(I+R)-1 : ℕ) (3/2 : ℝ)*smallGammaSum I R g ≤ C := by
  let f := fun g I R : ℕ => Real.rpow (2*g+(I+R)-1 : ℕ) (3/2 : ℝ)*smallGammaSum I R g
  have hf (g I R : ℕ) : 0≤f g I R := by
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (smallGammaSum_nonneg I R g)
  let C := 1+∑ g ∈ Finset.range 30, ∑ I ∈ Finset.range 30, ∑ R ∈ Finset.range 30, f g I R
  have hCsum : 0≤∑ g ∈ Finset.range 30, ∑ I ∈ Finset.range 30, ∑ R ∈ Finset.range 30, f g I R := by
    apply Finset.sum_nonneg
    intro g hg
    apply Finset.sum_nonneg
    intro I hI
    exact Finset.sum_nonneg (fun R hR => hf g I R)
  have hC : 0<C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro g I R hg hI hR
  have h₁ : f g I R≤∑ R ∈ Finset.range 30, f g I R :=
    Finset.single_le_sum (fun R hR => hf g I R) (Finset.mem_range.mpr hR)
  have h₂ : (∑ R ∈ Finset.range 30, f g I R)≤∑ I ∈ Finset.range 30, ∑ R ∈ Finset.range 30, f g I R :=
    Finset.single_le_sum (fun I hI => Finset.sum_nonneg (fun R hR => hf g I R)) (Finset.mem_range.mpr hI)
  have h₃ : (∑ I ∈ Finset.range 30, ∑ R ∈ Finset.range 30, f g I R)≤
      ∑ g ∈ Finset.range 30, ∑ I ∈ Finset.range 30, ∑ R ∈ Finset.range 30, f g I R :=
    Finset.single_le_sum (fun g hg => Finset.sum_nonneg (fun I hI => Finset.sum_nonneg (fun R hR => hf g I R)))
      (Finset.mem_range.mpr hg)
  exact h₁.trans (h₂.trans (h₃.trans (by dsimp only [C]; linarith)))
lemma partitionGamma_total_all : ∃ C : ℝ, 0<C ∧ ∀ {α : Type*} [DecidableEq α],
    ∀ A B : Finset α, Disjoint A B → ∀ g : ℕ, 2≤g →
    5*B.card≤3*(2*g+(A∪B).card-1) →
    (∑ i ∈ Finset.range (g+1), ∑ U ∈ (A∪B).powerset,
      partitionGammaTerm A g (A∪B).card i U) ≤
        C*(1+(A.card : ℝ))/Real.rpow (2*g+(A∪B).card-1 : ℕ) (3/2 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := partitionGamma_total
  obtain ⟨D,hD,hsmall⟩ := smallGammaSum_uniform
  refine ⟨C+D,by positivity,?_⟩
  intro α inst A B hAB g hg hR
  let n := (A∪B).card
  let h := 2*g+n-1
  have hh : 3≤h := by dsimp only [h]; omega
  have hhR : (0 : ℝ)<h := by exact_mod_cast (show 0<h by omega)
  have hp : 0<Real.rpow h (3/2 : ℝ) := Real.rpow_pos_of_pos hhR _
  by_cases hlarge : 30≤h
  · have hR' : 3*B.card≤2*((2*g+(A∪B).card-1)-3) := by
      change 3*B.card≤2*(h-3)
      change 5*B.card≤3*h at hR
      omega
    exact (hbound A B hAB g hg hR').trans (div_le_div_of_nonneg_right
      (by nlinarith [show (0 : ℝ)≤A.card by positivity]) hp.le)
  · have hcard := Finset.card_union_of_disjoint hAB
    have hg' : g<30 := by dsimp only [h,n] at *; omega
    have hA : A.card<30 := by dsimp only [h,n] at *; omega
    have hB : B.card<30 := by dsimp only [h,n] at *; omega
    rw [partitionGamma_sum_counts A B hAB]
    have he := hsmall g A.card B.card hg' hA hB
    rw [← hcard] at he
    have hsmallBound : smallGammaSum A.card B.card g≤D/Real.rpow h (3/2 : ℝ) := by
      apply (le_div_iff₀ hp).mpr
      nlinarith [he]
    exact hsmallBound.trans (div_le_div_of_nonneg_right
      (by nlinarith [show (0 : ℝ)≤A.card by positivity]) hp.le)
lemma actual_partitionGamma_total : ∃ C : ℝ, 0<C ∧ ∀ g pivot : ℕ, ∀ d : List ℕ, 2≤g →
    (pivot::d).sum≤dimension g (d.length+1) →
    (∑ i ∈ Finset.range (g+1), ∑ U ∈ (Finset.range d.length).powerset,
      partitionGammaTerm (inactiveIndices d) g d.length i U) ≤
        C*(1+(inactive d : ℝ))/Real.rpow (complexity g (d.length+1)) (3/2 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := partitionGamma_total_all
  refine ⟨C,hC,?_⟩
  intro g pivot d hg hd
  let A := inactiveIndices d
  let B := (Finset.range d.length)\A
  have hsub : A ⊆ Finset.range d.length := Finset.filter_subset _ _
  have hU : A∪B=Finset.range d.length := by
    dsimp only [B]
    ext j
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro (h | h)
      · exact hsub h
      · exact h.1
    · intro h
      by_cases hj : j∈A
      · exact Or.inl hj
      · exact Or.inr ⟨h,hj⟩
  have hAB : Disjoint A B := Finset.disjoint_left.mpr (by intro j hjA hjB; exact (Finset.mem_sdiff.mp hjB).2 hjA)
  have hAc : A.card=inactive d := inactiveIndices_card d
  have hBc : B.card=d.length-inactive d := by
    dsimp only [B]
    rw [Finset.card_sdiff_of_subset hsub,Finset.card_range,hAc]
  have hh : 2*g+d.length-1=complexity g (d.length+1) := by unfold complexity; omega
  have ht : d.length-inactive d≤(pivot::d).length-inactive (pivot::d) := by
    simp only [List.length_cons,inactive_cons_eq]
    split_ifs <;> have hi := inactive_le_length d <;> omega
  have ha := (active_dimension_bound g (pivot::d) hg (by simpa only [List.length_cons] using hd)).2
  have hR : 5*B.card≤3*(2*g+(A∪B).card-1) := by
    rw [hU,Finset.card_range,hBc,hh]
    simp only [List.length_cons] at ha ht
    omega
  have he := hbound A B hAB g hg hR
  rw [hU,Finset.card_range,hAc,hh] at he
  exact he
end WP
