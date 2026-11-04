import WPFormalization.Intersection.NormalizedBackground
/-! Ordered separating splits of finite background insertions. This derives
both the external/background split and the full product of binomial factors
for repeated background degrees, rather than postulating factorization. -/
noncomputable section
namespace WP
lemma sum_powerset_disjoint {α : Type*} [DecidableEq α] (A B : Finset α)
    (hAB : Disjoint A B) (F : Finset α → ℝ) :
    (∑ K ∈ (A ∪ B).powerset, F K) =
      ∑ I ∈ A.powerset, ∑ J ∈ B.powerset, F (I ∪ J) := by
  rw [Finset.sum_sigma']
  symm
  apply Finset.sum_bij (fun p _ => p.1 ∪ p.2)
  · intro p hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_sigma.mp hp
    apply Finset.mem_powerset.mpr
    exact Finset.union_subset_union (Finset.mem_powerset.mp hp₁) (Finset.mem_powerset.mp hp₂)
  · intro p hp q hq he
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_sigma.mp hq
    have hA : p.1 = q.1 := by
      ext x
      constructor
      · intro hx
        have hu : x ∈ q.1 ∪ q.2 := by rw [← he]; exact Finset.mem_union_left _ hx
        rcases Finset.mem_union.mp hu with hx' | hx'
        · exact hx'
        · exact False.elim (Finset.disjoint_left.mp hAB
            ((Finset.mem_powerset.mp hp₁) hx) ((Finset.mem_powerset.mp hq₂) hx'))
      · intro hx
        have hu : x ∈ p.1 ∪ p.2 := by rw [he]; exact Finset.mem_union_left _ hx
        rcases Finset.mem_union.mp hu with hx' | hx'
        · exact hx'
        · exact False.elim (Finset.disjoint_left.mp hAB
            ((Finset.mem_powerset.mp hq₁) hx) ((Finset.mem_powerset.mp hp₂) hx'))
    have hB : p.2 = q.2 := by
      ext x
      constructor
      · intro hx
        have hu : x ∈ q.1 ∪ q.2 := by rw [← he]; exact Finset.mem_union_right _ hx
        rcases Finset.mem_union.mp hu with hx' | hx'
        · exact False.elim (Finset.disjoint_left.mp hAB
            ((Finset.mem_powerset.mp hq₁) hx') ((Finset.mem_powerset.mp hp₂) hx))
        · exact hx'
      · intro hx
        have hu : x ∈ p.1 ∪ p.2 := by rw [he]; exact Finset.mem_union_right _ hx
        rcases Finset.mem_union.mp hu with hx' | hx'
        · exact False.elim (Finset.disjoint_left.mp hAB
            ((Finset.mem_powerset.mp hp₁) hx') ((Finset.mem_powerset.mp hq₂) hx))
        · exact hx'
    cases p
    cases q
    dsimp at hA hB
    subst_vars
    rfl
  · intro K hK
    have hsub := Finset.mem_powerset.mp hK
    refine ⟨⟨K ∩ A, K ∩ B⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      exact ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩
    · ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · tauto
      · intro hx
        rcases Finset.mem_union.mp (hsub hx) with ha | hb
        · exact Or.inl ⟨hx, ha⟩
        · exact Or.inr ⟨hx, hb⟩
  · intro p hp
    rfl
end WP
namespace WP
lemma selected_append_union (d e : List ℤ) (I J : Finset ℕ)
    (hI : I ⊆ Finset.range d.length) :
    selected (d ++ e) (I ∪ J.image (d.length+·)) = selected d I ++ selected e J := by
  have hleft : (List.range d.length).filter (fun i => i ∈ I ∪ J.image (d.length+·)) =
      (List.range d.length).filter (fun i => i ∈ I) := by
    apply List.filter_congr
    intro i hi
    have hin : i < d.length := by simpa using hi
    have hn : i ∉ J.image (d.length+·) := by
      intro he
      obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp he
      omega
    simp [hn]
  have hright : (List.range e.length).filter (fun i => d.length+i ∈ I ∪ J.image (d.length+·)) =
      (List.range e.length).filter (fun i => i ∈ J) := by
    apply List.filter_congr
    intro i hi
    have hn : d.length+i ∉ I := by
      intro he
      have hh := Finset.mem_range.mp (hI he)
      omega
    have himg : d.length+i ∈ J.image (d.length+·) ↔ i ∈ J := by
      constructor
      · intro he
        obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp he
        have heji : j = i := by omega
        simpa [heji] using hj
      · intro he
        exact Finset.mem_image.mpr ⟨i, he, rfl⟩
    simp [hn, himg]
  unfold selected
  rw [List.length_append, List.range_add, List.filter_append, List.map_append,
    List.filter_map, List.map_map]
  simp only [Function.comp_def]
  rw [hleft, hright]
  apply congrArg₂ (fun x y : List ℤ => x ++ y)
  · apply List.map_congr_left
    intro i hi
    have hin : i < d.length := by
      have := (List.mem_filter.mp hi).1
      simpa using this
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hin]
  · apply List.map_congr_left
    intro i hi
    simp only [List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (by omega : d.length ≤ d.length+i), Nat.add_sub_cancel_left]
end WP
namespace WP
lemma range_add_union (n m : ℕ) :
    Finset.range (n+m) = Finset.range n ∪ (Finset.range m).image (n+·) := by
  ext x
  simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
  constructor
  · intro hx
    by_cases hn : x < n
    · exact Or.inl hn
    · exact Or.inr ⟨x-n, by omega, by omega⟩
  · rintro (hx | ⟨j, hj, rfl⟩) <;> omega
lemma range_add_disjoint (n m : ℕ) :
    Disjoint (Finset.range n) ((Finset.range m).image (n+·)) := by
  apply Finset.disjoint_left.mpr
  intro x hx he
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
  have hn := Finset.mem_range.mp hx
  omega
lemma sdiff_union_disjoint {α : Type*} [DecidableEq α] (A B I J : Finset α)
    (hAB : Disjoint A B) (hI : I ⊆ A) (hJ : J ⊆ B) :
    (A ∪ B) \ (I ∪ J) = (A \ I) ∪ (B \ J) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨ha | hb, hn⟩
    · exact Or.inl ⟨ha, fun hi => hn (Or.inl hi)⟩
    · exact Or.inr ⟨hb, fun hj => hn (Or.inr hj)⟩
  · rintro (⟨ha, hn⟩ | ⟨hb, hn⟩)
    · refine ⟨Or.inl ha, ?_⟩
      rintro (hi | hj)
      · exact hn hi
      · exact Finset.disjoint_left.mp hAB ha (hJ hj)
    · refine ⟨Or.inr hb, ?_⟩
      rintro (hi | hj)
      · exact Finset.disjoint_left.mp hAB (hI hi) hb
      · exact hn hj
lemma append_selection_complement (n m : ℕ) (I J : Finset ℕ)
    (hI : I ⊆ Finset.range n) (hJ : J ⊆ Finset.range m) :
    (Finset.range (n+m)) \ (I ∪ J.image (n+·)) =
      ((Finset.range n) \ I) ∪ ((Finset.range m) \ J).image (n+·) := by
  rw [range_add_union, sdiff_union_disjoint _ _ _ _ (range_add_disjoint n m)
    hI (Finset.image_subset_image hJ), ← Finset.image_sdiff _ _ (by
      intro a b h
      exact Nat.add_left_cancel h)]
lemma sum_selected_append (d e : List ℤ) (F : List ℤ → List ℤ → ℝ) :
    (∑ K ∈ (Finset.range (d++e).length).powerset,
      F (selected (d++e) K) (selected (d++e) ((Finset.range (d++e).length) \ K))) =
    ∑ I ∈ (Finset.range d.length).powerset,
      ∑ J ∈ (Finset.range e.length).powerset,
        F (selected d I ++ selected e J)
          (selected d ((Finset.range d.length) \ I) ++ selected e ((Finset.range e.length) \ J)) := by
  simp only [List.length_append]
  rw [range_add_union, sum_powerset_disjoint _ _ (range_add_disjoint _ _)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.powerset_image, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro J hJ
    have hi := Finset.mem_powerset.mp hI
    have hj := Finset.mem_powerset.mp hJ
    rw [selected_append_union d e I J hi]
    rw [← range_add_union, append_selection_complement _ _ I J hi hj,
      selected_append_union d e _ _ Finset.sdiff_subset]
  · intro J hJ K hK he
    exact Finset.image_injective (by intro a b h; exact Nat.add_left_cancel h) he
end WP
namespace WP
lemma selected_replicate (n : ℕ) (a : ℤ) (I : Finset ℕ)
    (hI : I ⊆ Finset.range n) : selected (List.replicate n a) I = List.replicate I.card a := by
  let L := (List.range n).filter (fun i => i ∈ I)
  have hnd : L.Nodup := List.nodup_range.filter _
  have he : L.toFinset = I := by
    ext i
    simp only [L, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨And.right, fun hi => ⟨Finset.mem_range.mp (hI hi), hi⟩⟩
  have hlen : L.length = I.card := by
    have hh := List.toFinset_card_of_nodup hnd
    rw [he] at hh
    exact hh.symm
  unfold selected
  simp only [List.length_replicate]
  change L.map (fun i => (List.replicate n a)[i]!) = _
  calc
    L.map (fun i => (List.replicate n a)[i]!) = L.map (fun _ => a) := by
      apply List.map_congr_left
      intro i hi
      have hin : i < n := by
        have hh := (List.mem_filter.mp hi).1
        simpa using hh
      simp [hin]
    _ = List.replicate I.card a := by rw [List.map_const', hlen]
lemma sum_selected_replicate (n : ℕ) (a : ℤ) (F : List ℤ → List ℤ → ℝ) :
    (∑ I ∈ (Finset.range n).powerset,
      F (selected (List.replicate n a) I)
        (selected (List.replicate n a) ((Finset.range n) \ I))) =
    ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*
      F (List.replicate j a) (List.replicate (n-j) a) := by
  calc
    _ = ∑ I ∈ (Finset.range n).powerset,
        F (List.replicate I.card a) (List.replicate (n-I.card) a) := by
      apply Finset.sum_congr rfl
      intro I hI
      have hi := Finset.mem_powerset.mp hI
      rw [selected_replicate n a I hi,
        selected_replicate n a _ Finset.sdiff_subset, Finset.card_sdiff_of_subset hi, Finset.card_range]
    _ = _ := by
      have he := Finset.sum_powerset_apply_card
        (fun j => F (List.replicate j a) (List.replicate (n-j) a)) (x := Finset.range n)
      simpa only [Finset.card_range, nsmul_eq_mul] using he
end WP
namespace WP
def subBackgrounds {m : ℕ} (l : Fin m → ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (l i+1))
lemma mem_subBackgrounds {m : ℕ} (l j : Fin m → ℕ) :
    j ∈ subBackgrounds l ↔ ∀ i, j i ≤ l i := by
  simp only [subBackgrounds, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
lemma sum_subBackgrounds_succ {m : ℕ} (l : Fin (m+1) → ℕ)
    (F : (Fin (m+1) → ℕ) → ℝ) :
    (∑ j ∈ subBackgrounds l, F j) =
      ∑ q ∈ Finset.range (l (Fin.last m)+1),
        ∑ j ∈ subBackgrounds (Fin.init l), F (Fin.snoc j q) := by
  rw [Finset.sum_sigma']
  symm
  apply Finset.sum_bij (fun p _ => Fin.snoc p.2 p.1)
  · intro p hp
    obtain ⟨hplast, hpinit⟩ := Finset.mem_sigma.mp hp
    apply (mem_subBackgrounds l _).mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using Finset.mem_range.mp hplast
    · simpa [Fin.init] using (mem_subBackgrounds _ _).mp hpinit j
  · intro p hp q hq he
    have h₁ : p.1 = q.1 := by simpa using congrFun he (Fin.last m)
    have h₂ : p.2 = q.2 := by
      funext i
      simpa using congrFun he i.castSucc
    cases p
    cases q
    dsimp at h₁ h₂
    subst_vars
    rfl
  · intro j hj
    refine ⟨⟨j (Fin.last m), Fin.init j⟩, ?_, Fin.snoc_init_self j⟩
    apply Finset.mem_sigma.mpr
    constructor
    · change j (Fin.last m) ∈ Finset.range (l (Fin.last m)+1)
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((mem_subBackgrounds l j).mp hj (Fin.last m)))
    · apply (mem_subBackgrounds _ _).mpr
      intro i
      exact (mem_subBackgrounds l j).mp hj i.castSucc
  · intro p hp
    rfl
lemma backgroundDegrees_snoc {m : ℕ} (l : Fin (m+1) → ℕ) :
    backgroundDegrees l = backgroundDegrees (Fin.init l) ++
      List.replicate (l (Fin.last m)) (m+2) := by
  unfold backgroundDegrees
  rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
  simp [Fin.init]
lemma subBackgrounds_zero (l : Fin 0 → ℕ) : subBackgrounds l = {0} := by
  ext j
  have he : j = 0 := Subsingleton.elim _ _
  subst j
  simp [mem_subBackgrounds]
end WP
namespace WP
lemma sum_selected_background {m : ℕ} (l : Fin m → ℕ)
    (F : List ℤ → List ℤ → ℝ) :
    (∑ I ∈ (Finset.range (backgroundDegrees l).length).powerset,
      F (selected ((backgroundDegrees l).map Int.ofNat) I)
        (selected ((backgroundDegrees l).map Int.ofNat) ((Finset.range (backgroundDegrees l).length) \ I))) =
    ∑ j ∈ subBackgrounds l, (∏ i, ((l i).choose (j i) : ℝ))*
      F ((backgroundDegrees j).map Int.ofNat) ((backgroundDegrees (fun i => l i-j i)).map Int.ofNat) := by
  induction m generalizing F with
  | zero => simp [backgroundDegrees, subBackgrounds_zero, selected]
  | succ m ih =>
    let L := (backgroundDegrees (Fin.init l)).map Int.ofNat
    let n := l (Fin.last m)
    let a : ℤ := m+2
    have hl : (backgroundDegrees l).map Int.ofNat = L ++ List.replicate n a := by
      rw [backgroundDegrees_snoc, List.map_append, List.map_replicate]
      rfl
    have hlen : (backgroundDegrees l).length = (L ++ List.replicate n a).length := by
      rw [← List.length_map (f := Int.ofNat), hl]
    rw [hlen, hl, sum_selected_append]
    have hinner (I : Finset ℕ) :
        (∑ J ∈ (Finset.range (List.replicate n a).length).powerset,
          F (selected L I ++ selected (List.replicate n a) J)
            (selected L ((Finset.range L.length) \ I) ++
              selected (List.replicate n a) ((Finset.range (List.replicate n a).length) \ J))) =
        ∑ q ∈ Finset.range (n+1), (n.choose q : ℝ)*
          F (selected L I ++ List.replicate q a)
            (selected L ((Finset.range L.length) \ I) ++ List.replicate (n-q) a) := by
      simpa only [List.length_replicate] using
        sum_selected_replicate n a (fun x y => F (selected L I ++ x)
          (selected L ((Finset.range L.length) \ I) ++ y))
    rw [Finset.sum_congr rfl (fun I _ => hinner I), Finset.sum_comm]
    calc
      _ = ∑ q ∈ Finset.range (n+1), (n.choose q : ℝ)*
          (∑ I ∈ (Finset.range L.length).powerset,
            F (selected L I ++ List.replicate q a)
              (selected L ((Finset.range L.length) \ I) ++ List.replicate (n-q) a)) := by
        simp only [Finset.mul_sum]
      _ = ∑ q ∈ Finset.range (n+1), ∑ j ∈ subBackgrounds (Fin.init l),
          (n.choose q : ℝ)*((∏ i, (((Fin.init l) i).choose (j i) : ℝ))*
            F ((backgroundDegrees j).map Int.ofNat ++ List.replicate q a)
              ((backgroundDegrees (fun i => (Fin.init l) i-j i)).map Int.ofNat ++ List.replicate (n-q) a)) := by
        apply Finset.sum_congr rfl
        intro q hq
        have he := ih (Fin.init l) (fun x y => F (x ++ List.replicate q a) (y ++ List.replicate (n-q) a))
        rw [show L.length = (backgroundDegrees (Fin.init l)).length by simp [L], he, Finset.mul_sum]
      _ = _ := by
        rw [sum_subBackgrounds_succ]
        apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro j hj
        have hbg : (backgroundDegrees (Fin.snoc j q)).map Int.ofNat =
            (backgroundDegrees j).map Int.ofNat ++ List.replicate q a := by
          rw [backgroundDegrees_snoc]
          simp [a]
        have hbg' : (backgroundDegrees (fun i : Fin (m+1) => l i-(Fin.snoc j q : Fin (m+1) → ℕ) i)).map Int.ofNat =
            (backgroundDegrees (fun i => (Fin.init l) i-j i)).map Int.ofNat ++ List.replicate (n-q) a := by
          rw [backgroundDegrees_snoc]
          simp [a, n, Fin.init]
          apply congrArg (fun v : Fin m → ℕ => (backgroundDegrees v).map Int.ofNat)
          funext i
          simp [Fin.init]
        rw [hbg, hbg', Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        dsimp only [n, Fin.init]
        ring
end WP
