import WPFormalization.Weighted.TransitionWeights
import WPFormalization.Weighted.LabelSum

/-! Exact active/inactive label-subset counting, with the genuine selected degrees. -/
noncomputable section
namespace WP
lemma sum_powerset_two_colors {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (f : ℕ → ℕ → ℝ) :
    (∑ U ∈ (A∪B).powerset, f (U∩A).card (U∩B).card) =
      ∑ U ∈ A.powerset, ∑ V ∈ B.powerset, f U.card V.card := by
  rw [← Finset.sum_product (f := fun UV : Finset α × Finset α => f UV.1.card UV.2.card)]
  apply Finset.sum_bij (fun U hU => (U∩A,U∩B))
  · intro U hU
    simp only [Finset.mem_product,Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right,Finset.inter_subset_right⟩
  · intro U hU V hV he
    have hUs := Finset.mem_powerset.mp hU
    have hVs := Finset.mem_powerset.mp hV
    have heA := congrArg Prod.fst he
    have heB := congrArg Prod.snd he
    dsimp only at heA heB
    ext x
    have hxU : x ∈ U → x ∈ A ∨ x ∈ B := by intro h; exact Finset.mem_union.mp (hUs h)
    have hxV : x ∈ V → x ∈ A ∨ x ∈ B := by intro h; exact Finset.mem_union.mp (hVs h)
    have heAm : x ∈ U ∩ A ↔ x ∈ V ∩ A := by rw [heA]
    have heBm : x ∈ U ∩ B ↔ x ∈ V ∩ B := by rw [heB]
    simp only [Finset.mem_inter] at heAm heBm
    tauto
  · intro UV hUV
    have hU := Finset.mem_powerset.mp (Finset.mem_product.mp hUV).1
    have hV := Finset.mem_powerset.mp (Finset.mem_product.mp hUV).2
    refine ⟨UV.1∪UV.2,Finset.mem_powerset.mpr (Finset.union_subset_union hU hV),?_⟩
    have hd : ∀ x, x ∈ A → x ∈ B → False := by
      intro x hxA hxB
      exact Finset.disjoint_left.mp hAB hxA hxB
    apply Prod.ext
    · ext x
      simp only [Finset.mem_inter,Finset.mem_union]
      constructor
      · rintro ⟨h | h,hA⟩
        · exact h
        · exact False.elim (hd x hA (hV h))
      · intro h
        exact ⟨Or.inl h,hU h⟩
    · ext x
      simp only [Finset.mem_inter,Finset.mem_union]
      constructor
      · rintro ⟨h | h,hB⟩
        · exact False.elim (hd x (hU h) hB)
        · exact h
      · intro h
        exact ⟨Or.inr h,hV h⟩
  · intro U hU
    rfl
lemma sum_powerset_two_colors_choose {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (f : ℕ → ℕ → ℝ) :
    (∑ U ∈ (A∪B).powerset, f (U∩A).card (U∩B).card) =
      ∑ u ∈ Finset.range (A.card+1), ∑ v ∈ Finset.range (B.card+1),
        (A.card.choose u : ℝ)*(B.card.choose v : ℝ)*f u v := by
  rw [sum_powerset_two_colors A B hAB f,
    Finset.sum_powerset_apply_card (fun u => ∑ V ∈ B.powerset, f u V.card)]
  simp only [Finset.sum_powerset_apply_card,nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring
def selectedNat (d : List ℕ) (I : Finset ℕ) : List ℕ :=
  ((List.range d.length).filter (fun j => j ∈ I)).map (fun j => d[j]!)
def inactiveIndices (d : List ℕ) : Finset ℕ :=
  (Finset.range d.length).filter (fun j => d[j]! ≤ 1)
lemma selectedNat_inactive (d : List ℕ) (I : Finset ℕ) :
    inactive (selectedNat d I) = (I∩inactiveIndices d).card := by
  unfold selectedNat inactive
  rw [List.filter_map]
  simp only [List.length_map]
  have hn := ((List.nodup_range : (List.range d.length).Nodup).filter (fun j => decide (j∈I))).filter
    ((fun k : ℕ => decide (k≤1)) ∘ fun j => d[j]!)
  have he : ((((List.range d.length).filter (fun j => j∈I)).filter
      ((fun k : ℕ => decide (k≤1)) ∘ fun j => d[j]!))).toFinset = I∩inactiveIndices d := by
    ext j
    simp only [List.mem_toFinset,List.mem_filter,List.mem_range,Function.comp_apply,decide_eq_true_eq,
      Finset.mem_inter,inactiveIndices,Finset.mem_filter,Finset.mem_range]
    tauto
  rw [← List.toFinset_card_of_nodup hn,he]
lemma selectedNat_ofNat (d : List ℕ) (I : Finset ℕ) :
    (selectedNat d I).map Int.ofNat = selected (d.map Int.ofNat) I := by
  unfold selectedNat selected
  simp only [List.length_map,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
  simp [hj']
lemma selectedNat_length (d : List ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range d.length) :
    (selectedNat d I).length=I.card := by
  have he : ((List.range d.length).filter (fun j => j∈I)).toFinset=I := by
    ext j
    simp only [List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨Finset.mem_range.mp (hI h),h⟩
  unfold selectedNat
  rw [List.length_map,← List.toFinset_card_of_nodup ((List.nodup_range : (List.range d.length).Nodup).filter (fun j => decide (j∈I))),he]
lemma selectedNat_partition_perm (d : List ℕ) (I : Finset ℕ) :
    ((selectedNat d I)++(selectedNat d ((Finset.range d.length)\I))).Perm d := by
  have he := selected_partition_perm (d.map Int.ofNat) I
  simp only [List.length_map] at he
  rw [← selectedNat_ofNat,← selectedNat_ofNat,← List.map_append] at he
  have hh := he.map Int.toNat
  simp only [List.map_map,Function.comp_def] at hh
  change (((selectedNat d I)++(selectedNat d ((Finset.range d.length)\I))).map (fun x => x)).Perm (d.map (fun x => x)) at hh
  simpa only [List.map_id_fun',id_eq] using hh
lemma inactiveIndices_card (d : List ℕ) : (inactiveIndices d).card=inactive d := by
  have hempty : selectedNat d ∅=[] := by simp [selectedNat]
  have hp : (selectedNat d (Finset.range d.length)).Perm d := by
    simpa only [Finset.sdiff_self,hempty,List.append_nil] using
      selectedNat_partition_perm d (Finset.range d.length)
  have he := selectedNat_inactive d (Finset.range d.length)
  have hsub : inactiveIndices d ⊆ Finset.range d.length := Finset.filter_subset _ _
  rw [inactive_perm hp,Finset.inter_eq_right.mpr hsub] at he
  exact he.symm
lemma selectedNat_active (d : List ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range d.length) :
    (selectedNat d I).length-inactive (selectedNat d I) =
      (I∩((Finset.range d.length)\inactiveIndices d)).card := by
  rw [selectedNat_length d I hI,selectedNat_inactive]
  have he : I∩((Finset.range d.length)\inactiveIndices d)=I\inactiveIndices d := by
    ext j
    simp only [Finset.mem_inter,Finset.mem_sdiff]
    constructor
    · intro h; exact ⟨h.1,h.2.2⟩
    · intro h; exact ⟨h.1,hI h.1,h.2⟩
  rw [he]
  have hc := Finset.card_inter_add_card_sdiff I (inactiveIndices d)
  omega
lemma binomial_grid_antidiagonal (I R s : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ u, I<u → f u=0) (hg : ∀ v, R<v → g v=0) :
    (∑ u ∈ Finset.range (I+1), ∑ v ∈ Finset.range (R+1),
      if u+v=s then f u*g v else 0) =
      ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal s, f uv.1*g uv.2 := by
  rw [← Finset.sum_product (f := fun uv : ℕ × ℕ => if uv.1+uv.2=s then f uv.1*g uv.2 else 0)]
  apply Finset.sum_bij_ne_zero (fun uv huv hnon => uv)
  · intro uv huv hnon
    apply Finset.HasAntidiagonal.mem_antidiagonal.mpr
    by_contra h
    exact hnon (if_neg h)
  · intro uv huv hnon uv' huv' hnon' he
    exact he
  · intro uv huv hnon
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    have hu : uv.1 ≤ I := by
      by_contra h
      exact hnon (by rw [hf uv.1 (by omega),zero_mul])
    have hv : uv.2 ≤ R := by
      by_contra h
      exact hnon (by rw [hg uv.2 (by omega),mul_zero])
    refine ⟨uv,Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,?_,rfl⟩
    simpa only [he,ite_true] using hnon
  · intro uv huv hnon
    have he : uv.1+uv.2=s := by
      by_contra h
      exact hnon (if_neg h)
    simp only [he,ite_true]
lemma powerset_label_envelope {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (s : ℕ) :
    (∑ U ∈ (A∪B).powerset, if U.card=s then
      1/Real.sqrt (A.card.choose (U∩A).card) else 0) = weightedLabelSum A.card B.card s := by
  have hcard (U : Finset α) (hU : U ∈ (A∪B).powerset) : U.card=(U∩A).card+(U∩B).card := by
    have hUs := Finset.mem_powerset.mp hU
    have hd : ∀ x, x∈A → x∈B → False := fun x hxA hxB => Finset.disjoint_left.mp hAB hxA hxB
    have he : U\A=U∩B := by
      ext x
      simp only [Finset.mem_sdiff,Finset.mem_inter]
      have hh : x∈U → x∈A ∨ x∈B := fun hx => Finset.mem_union.mp (hUs hx)
      constructor
      · intro h
        exact ⟨h.1,(hh h.1).resolve_left h.2⟩
      · intro h
        exact ⟨h.1,fun hxA => hd x hxA h.2⟩
    have hc := Finset.card_inter_add_card_sdiff U A
    rw [he] at hc
    exact hc.symm
  calc
    _ = ∑ U ∈ (A∪B).powerset, if (U∩A).card+(U∩B).card=s then
        1/Real.sqrt (A.card.choose (U∩A).card) else 0 := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [hcard U hU]
    _ = ∑ u ∈ Finset.range (A.card+1), ∑ v ∈ Finset.range (B.card+1),
        (A.card.choose u : ℝ)*(B.card.choose v : ℝ)*
          (if u+v=s then 1/Real.sqrt (A.card.choose u) else 0) :=
      sum_powerset_two_colors_choose A B hAB (fun u v => if u+v=s then 1/Real.sqrt (A.card.choose u) else 0)
    _ = ∑ u ∈ Finset.range (A.card+1), ∑ v ∈ Finset.range (B.card+1),
        if u+v=s then Real.sqrt (A.card.choose u)*(B.card.choose v : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      split_ifs
      · rw [show (A.card.choose u : ℝ)*(B.card.choose v : ℝ)*(1/Real.sqrt (A.card.choose u)) =
          ((A.card.choose u : ℝ)/Real.sqrt (A.card.choose u))*(B.card.choose v : ℝ) by ring,Real.div_sqrt]
      · ring
    _ = _ := binomial_grid_antidiagonal A.card B.card s
      (fun u => Real.sqrt (A.card.choose u)) (fun v => (B.card.choose v : ℝ))
      (by intro u hu; simp [Nat.choose_eq_zero_of_lt hu])
      (by intro v hv; simp [Nat.choose_eq_zero_of_lt hv])
lemma powerset_actual_label_envelope (d : List ℕ) (s : ℕ) :
    (∑ U ∈ (Finset.range d.length).powerset, if U.card=s then
      1/Real.sqrt ((inactive d).choose (inactive (selectedNat d U))) else 0) =
      weightedLabelSum (inactive d) (d.length-inactive d) s := by
  let A := inactiveIndices d
  let B := (Finset.range d.length)\A
  have hsub : A ⊆ Finset.range d.length := Finset.filter_subset _ _
  have hU : A∪B=Finset.range d.length := by
    dsimp only [B]
    ext j
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · intro h
      rcases h with h | h
      · exact hsub h
      · exact h.1
    · intro h
      by_cases hj : j∈A
      · exact Or.inl hj
      · exact Or.inr ⟨h,hj⟩
  have hAB : Disjoint A B := Finset.disjoint_left.mpr (by
    intro j hjA hjB
    exact (Finset.mem_sdiff.mp hjB).2 hjA)
  have hAc : A.card=inactive d := inactiveIndices_card d
  have hBc : B.card=d.length-inactive d := by
    dsimp only [B]
    rw [Finset.card_sdiff_of_subset hsub,Finset.card_range,hAc]
  have he := powerset_label_envelope A B hAB s
  rw [hU,hAc,hBc] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [selectedNat_inactive]
end WP
