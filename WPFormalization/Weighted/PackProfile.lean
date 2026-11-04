import WPFormalization.Weighted.PackConvolution
import WPFormalization.Weighted.PartitionSum
import WPFormalization.Weighted.PartitionProfile

/-! Every actual separating pack is dominated by the proved Gamma/label envelope, with unstable and genus-zero empty supports handled explicitly; the left/right involution orients the finite mass. -/
noncomputable section
namespace WP
lemma separatingPack_unstable_left (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l i : ℕ) (I : Finset ℕ)
    (hs : ¬ Stable i ((selectedNat d I).length+1)) :
    separatingPack c Y g pivot d l (i,I)=0 := by
  unfold separatingPack
  apply Finset.sum_eq_zero
  intro u hu
  unfold separatingNodeTerm
  dsimp only
  rw [← selectedNat_ofNat d I]
  have hs' : ¬ Stable i ((u : ℤ)::(selectedNat d I).map Int.ofNat).length := by
    simpa only [List.length_cons,List.length_map] using hs
  rw [validModel_unstable_zero i _ Y hs']
  ring
lemma separatingPack_unstable_right (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l i : ℕ) (I : Finset ℕ)
    (hs : ¬ Stable (g-i) ((selectedNat d ((Finset.range d.length)\I)).length+1)) :
    separatingPack c Y g pivot d l (i,I)=0 := by
  unfold separatingPack
  apply Finset.sum_eq_zero
  intro u hu
  unfold separatingNodeTerm
  dsimp only
  rw [← selectedNat_ofNat d ((Finset.range d.length)\I)]
  have hs' : ¬ Stable (g-i) (((pivot : ℤ)+l-2-u)::(selectedNat d ((Finset.range d.length)\I)).map Int.ofNat).length := by
    simpa only [List.length_cons,List.length_map] using hs
  rw [validModel_unstable_zero (g-i) _ Y hs']
  ring
lemma separatingPack_profile_on_support (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ, 0<C ∧ ∀ g pivot : ℕ, ∀ d : List ℕ, 2≤g →
      (pivot::d).sum≤dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
      ∀ l : ℕ, l≤deficit g (pivot::d) → ∀ i : ℕ, i≤g → ∀ I : Finset ℕ, I ⊆ Finset.range d.length →
      Stable i ((selectedNat d I).length+1) →
      Stable (g-i) ((selectedNat d ((Finset.range d.length)\I)).length+1) →
      2*i+I.card-1≤2*(g-i)+(d.length-I.card)-1 → (i≠0 ∨ 2≤(I∩inactiveIndices d).card) →
      separatingPack c Y g pivot d l (i,I)≤
        C/6*linearQ Y (complexity g (d.length+1)) (deficit g (pivot::d)) l*
          partitionGammaTerm (inactiveIndices d) g d.length i I := by
  obtain ⟨C,hC,hbound⟩ := clippedWeight_partition_profile c hc
  refine ⟨C,hC,?_⟩
  intro g pivot d hg hd Y hY l hl i hi I hI hs₁ hs₂ hsmall hq
  let e₁ := selectedNat d I
  let e₂ := selectedNat d ((Finset.range d.length)\I)
  let h₁ := complexity i (e₁.length+1)
  let h₂ := complexity (g-i) (e₂.length+1)
  let h := complexity g (d.length+1)
  have hp : (e₁++e₂).Perm d := selectedNat_partition_perm d I
  have he₁ : e₁.length=I.card := selectedNat_length d I hI
  have he₂ : e₂.length=d.length-I.card := by
    have he := hp.length_eq
    simp only [List.length_append] at he
    omega
  have hc₁ : h₁=2*i+I.card-1 := by dsimp only [h₁]; rw [he₁]; unfold complexity; omega
  have hc₂ : h₂=2*(g-i)+(d.length-I.card)-1 := by dsimp only [h₂]; rw [he₂]; unfold complexity; omega
  have hpar : h=2*g+d.length-1 := by dsimp only [h]; unfold complexity; omega
  have hsmall' : h₁≤h₂ := by omega
  have hAc : (inactiveIndices d).card=inactive d := inactiveIndices_card d
  have hIc : (I∩inactiveIndices d).card=inactive e₁ := (selectedNat_inactive d I).symm
  let B : ℝ := (((I.card : ℝ)+2)*Real.sqrt h/Real.sqrt ((inactive d).choose (inactive e₁)))*
    Real.exp ((1/12 : ℝ)*min h₁ h₂)
  have hB : 0≤B := by dsimp only [B]; positivity
  have hnode := separatingPack_node_bound c Y g pivot d l i I hi hd hl hY hs₁ hs₂ (C*B) (mul_nonneg hC.le hB) (by
    intro u hu
    have he := mul_le_mul_of_nonneg_right (hbound g hg pivot d I hI u (pivot+l-2-u))
      (Real.exp_pos ((1/12 : ℝ)*min h₁ h₂)).le
    convert he using 1 <;> dsimp only [B,h₁,h₂,h,e₁,e₂] <;> ring)
  have hh₁ : 1≤2*i+I.card-1 := by
    unfold Stable at hs₁
    change 3≤2*i+(e₁.length+1) at hs₁
    rw [he₁] at hs₁
    omega
  have hh₂ : 1≤2*(g-i)+(d.length-I.card)-1 := by
    unfold Stable at hs₂
    change 3≤2*(g-i)+(e₂.length+1) at hs₂
    rw [he₂] at hs₂
    omega
  have hΓ : partitionGammaTerm (inactiveIndices d) g d.length i I =
      (Real.Gamma h₁*Real.Gamma h₂/Real.Gamma h)*B := by
    unfold partitionGammaTerm
    dsimp only
    rw [if_pos ⟨hh₁,hh₂,hsmall,hq⟩]
    rw [← hc₁,← hc₂,← hpar,hAc,hIc]
    dsimp only [B]
    rw [Nat.min_eq_left hsmall']
    have he : Real.exp ((h₁ : ℝ)/12)=Real.exp ((1/12 : ℝ)*h₁) := by congr 1; ring
    rw [he]
    ring
  apply hnode.trans_eq
  change (Real.Gamma h₁*Real.Gamma h₂/Real.Gamma h)/6*
      linearQ Y h (deficit g (pivot::d)) l*(C*B)=_
  rw [hΓ]
  ring
lemma separatingPack_profile (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ, 0<C ∧ ∀ g pivot : ℕ, ∀ d : List ℕ, 2≤g →
      (pivot::d).sum≤dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
      ∀ l : ℕ, l≤deficit g (pivot::d) → ∀ i : ℕ, i≤g → ∀ I : Finset ℕ, I ⊆ Finset.range d.length →
      2*i+I.card-1≤2*(g-i)+(d.length-I.card)-1 →
      separatingPack c Y g pivot d l (i,I)≤
        C/6*linearQ Y (complexity g (d.length+1)) (deficit g (pivot::d)) l*
          partitionGammaTerm (inactiveIndices d) g d.length i I := by
  obtain ⟨C,hC,hbound⟩ := separatingPack_profile_on_support c hc
  refine ⟨C,hC,?_⟩
  intro g pivot d hg hd Y hY l hl i hi I hI hsmall
  have he₁ : (selectedNat d I).length=I.card := selectedNat_length d I hI
  have he₂ : (selectedNat d ((Finset.range d.length)\I)).length=d.length-I.card := by
    have he := (selectedNat_partition_perm d I).length_eq
    simp only [List.length_append,he₁] at he
    omega
  by_cases hs₁ : Stable i ((selectedNat d I).length+1)
  · by_cases hs₂ : Stable (g-i) ((selectedNat d ((Finset.range d.length)\I)).length+1)
    · by_cases hq : i≠0 ∨ 2≤(I∩inactiveIndices d).card
      · exact hbound g pivot d hg hd Y hY l hl i hi I hI hs₁ hs₂ hsmall hq
      · have hΓzero : partitionGammaTerm (inactiveIndices d) g d.length i I=0 := by
          unfold partitionGammaTerm
          dsimp only
          apply if_neg
          intro h
          exact hq h.2.2.2
        have hi0 : i=0 := by
          by_contra h
          exact hq (Or.inl h)
        have hInactive : inactive (selectedNat d I)<2 := by
          rw [selectedNat_inactive]
          have hn : ¬ 2≤(I∩inactiveIndices d).card := fun h => hq (Or.inr h)
          omega
        have hempty := separatingValidNodes_genus_zero_empty (g-i) pivot l (selectedNat d I)
          (selectedNat d ((Finset.range d.length)\I)) (by simpa only [hi0] using hs₁) hInactive
        have hempty' : separatingValidNodes i (g-i) pivot l (selectedNat d I)
            (selectedNat d ((Finset.range d.length)\I))=∅ := by simpa only [hi0] using hempty
        have hnode := separatingPack_node_bound c Y g pivot d l i I hi hd hl hY hs₁ hs₂ 0 (le_rfl) (by
          intro u hu
          rw [hempty'] at hu
          exact False.elim (Finset.notMem_empty u hu))
        simpa only [hΓzero,mul_zero] using hnode
    · have hΓzero : partitionGammaTerm (inactiveIndices d) g d.length i I=0 := by
        unfold partitionGammaTerm
        dsimp only
        apply if_neg
        intro h
        apply hs₂
        unfold Stable
        rw [he₂]
        have hp := h.2.1
        omega
      rw [separatingPack_unstable_right c Y g pivot d l i I hs₂,hΓzero,mul_zero]
  · have hΓzero : partitionGammaTerm (inactiveIndices d) g d.length i I=0 := by
      unfold partitionGammaTerm
      dsimp only
      apply if_neg
      intro h
      apply hs₁
      unfold Stable
      rw [he₁]
      have hp := h.1
      omega
    rw [separatingPack_unstable_left c Y g pivot d l i I hs₁,hΓzero,mul_zero]
def separatingOrientation (g n : ℕ) (iU : ℕ × Finset ℕ) : Prop :=
  2*iU.1+iU.2.card-1≤2*(g-iU.1)+(n-iU.2.card)-1
instance separatingOrientation_decidable (g n : ℕ) (iU : ℕ × Finset ℕ) :
    Decidable (separatingOrientation g n iU) := by
  unfold separatingOrientation
  infer_instance
lemma separatingOrientation_cover (g n : ℕ) (iU : ℕ × Finset ℕ)
    (hiU : iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range n).powerset) :
    separatingOrientation g n iU ∨ separatingOrientation g n (separatingLabelSwap g n iU) := by
  have hi := Finset.mem_range.mp (Finset.mem_product.mp hiU).1
  have hU := Finset.mem_powerset.mp (Finset.mem_product.mp hiU).2
  have hcard := Finset.card_le_card hU
  simp only [Finset.card_range] at hcard
  have hc : ((Finset.range n)\iU.2).card=n-iU.2.card := by rw [Finset.card_sdiff_of_subset hU,Finset.card_range]
  unfold separatingOrientation separatingLabelSwap
  dsimp only
  rw [hc,show g-(g-iU.1)=iU.1 by omega,show n-(n-iU.2.card)=iU.2.card by omega]
  exact le_total _ _
lemma weightedSeparating_orientation (c Y : ℝ) (g pivot : ℕ) (d : List ℕ)
    (hg : 2≤g) (hY : Y ∈ Set.Icc 0 y₀) :
    weightedSeparating c Y g pivot d≤
      2*(∑ l ∈ Finset.range (deficit g (pivot::d)+1),
        ∑ iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range d.length).powerset,
          if separatingOrientation g d.length iU then separatingPack c Y g pivot d l iU else 0) := by
  classical
  rw [weightedSeparating_eq_packs]
  calc
    _ ≤ ∑ l ∈ Finset.range (deficit g (pivot::d)+1),
        2*(∑ iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range d.length).powerset,
          if separatingOrientation g d.length iU then separatingPack c Y g pivot d l iU else 0) := by
      apply Finset.sum_le_sum
      intro l hl
      apply sum_le_twice_oriented _ (separatingLabelSwap g d.length) (separatingPack c Y g pivot d l)
        (separatingOrientation g d.length)
      · exact separatingLabelSwap_mem g d.length
      · exact separatingLabelSwap_involutive g d.length
      · exact separatingPack_swap c Y g pivot d l
      · intro iU hiU
        unfold separatingPack
        exact Finset.sum_nonneg (fun u hu => separatingNodeTerm_nonneg c Y g pivot d l u iU.1 iU.2 hg hY)
      · exact separatingOrientation_cover g d.length
    _ = _ := (Finset.mul_sum _ _ _).symm
end WP
