import WPFormalization.Marked.SecondSeparatingDecomposition

/-! The actual sphere and torus initial amplitudes and the finite zero-label pair count. -/

noncomputable section
open Set

noncomputable section
open Set
namespace WP
lemma selected_nat_nonneg (d : List ℕ) (I : Finset ℕ) :
    ∀ k ∈ selected (d.map Int.ofNat) I, 0 ≤ k := by
  intro k hk
  unfold selected at hk
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
  have hj' := (List.mem_filter.mp hj).1
  have hjn : j<d.length := by simpa only [List.length_map,List.mem_range] using hj'
  simpa [hjn] using (Int.natCast_nonneg (d[j]!))

lemma selected_nat_zero_iff (d : List ℕ) (I : Finset ℕ) (hI : I⊆Finset.range d.length) :
    (∀ k ∈ selected (d.map Int.ofNat) I, k=0) ↔ ∀ j∈I,d[j]! = 0 := by
  constructor
  · intro hz j hj
    have hjn := Finset.mem_range.mp (hI hj)
    have hmem : ((d[j]!:ℕ):ℤ) ∈ selected (d.map Int.ofNat) I := by
      unfold selected
      apply List.mem_map.mpr
      refine ⟨j,?_,?_⟩
      · simp only [List.mem_filter,List.mem_range,List.length_map,decide_eq_true_eq]
        exact ⟨hjn,hj⟩
      · simp [hjn]
    exact_mod_cast hz _ hmem
  · intro hz k hk
    unfold selected at hk
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
    have hj' := List.mem_filter.mp hj
    have hjn : j<d.length := by simpa only [List.length_map,List.mem_range] using hj'.1
    have hjI : j∈I := of_decide_eq_true hj'.2
    have hzero : d[j] = 0 := by simpa [hjn] using hz j hjI
    simp [hjn,hzero]

lemma normInt_sphere_three (P : PsiTheory) (d : List ℤ) (hlen : d.length=3)
    (hn : ∀ k∈d,0 ≤ k) (Y : ℝ) (hY : Y∈Icc 0 y₀) :
    normInt P 0 d Y=(if ∀ k∈d,k=0 then 1 else 0) := by
  classical
  unfold normInt
  rw [if_pos hn]
  by_cases hz : ∀ k∈d,k=0
  · have he : d=List.replicate 3 0 := List.eq_replicate_iff.mpr ⟨hlen,hz⟩
    rw [if_pos hz,he]
    simpa using (initial_amplitudes P Y hY).1
  · rw [if_neg hz]
    apply normalized_excess P 0 _ Y
    have hs : (d.map Int.toNat).sum≠0 := by
      intro hs
      have hall := List.sum_eq_zero_iff.mp hs
      apply hz
      intro k hk
      have hk0 := hall (Int.toNat k) (List.mem_map.mpr ⟨k,hk,rfl⟩)
      have hkn := hn k hk
      omega
    simp only [List.length_map,hlen,dimension]
    omega

lemma normInt_sphere_selected (P : PsiTheory) (d : List ℕ) (u : ℕ) (I : Finset ℕ)
    (hI : I⊆Finset.range d.length) (hcard : I.card=2) (Y : ℝ) (hY : Y∈Icc 0 y₀) :
    normInt P 0 ((u:ℤ)::selected (d.map Int.ofNat) I) Y=
      (if u=0 ∧ ∀ j∈I,d[j]! = 0 then 1 else 0) := by
  classical
  have hlen := selected_length_card (d.map Int.ofNat) I (by simpa only [List.length_map] using hI)
  rw [normInt_sphere_three P _ (by simp only [List.length_cons,hlen,hcard]) (by
    intro k hk
    rcases List.mem_cons.mp hk with rfl|hk
    · positivity
    · exact selected_nat_nonneg d I k hk) Y hY]
  have hz : (∀ k∈((u:ℤ)::selected (d.map Int.ofNat) I),k=0) ↔ u=0 ∧ ∀j∈I,d[j]! = 0 := by
    rw [List.forall_mem_cons,selected_nat_zero_iff d I hI]
    simp
  exact if_congr hz rfl rfl

lemma normInt_torus_one (P : PsiTheory) (u : ℕ) (Y : ℝ) (hY : Y∈Icc 0 y₀) :
    (4:ℝ)*normInt P 1 [(u:ℤ)] Y=
      (if u=0 then theta Y 1/2 else if u=1 then 1/2 else 0) := by
  have hn : ∀ k∈[(u:ℤ)],0 ≤ k := by simp
  unfold normInt
  rw [if_pos hn]
  simp only [List.map_cons,List.map_nil,Int.toNat_natCast]
  by_cases h0 : u=0
  · subst u
    rw [(initial_amplitudes P Y hY).2.2]
    norm_num <;> ring
  · by_cases h1 : u=1
    · subst u
      rw [(initial_amplitudes P Y hY).2.1]
      norm_num <;> ring
    · rw [if_neg h0,if_neg h1,normalized_excess P 1 [u] Y (by simp [dimension,List.sum_cons];omega)]
      ring
end WP

namespace WP
lemma selected_nat_toNat_sublist (d : List ℕ) (I : Finset ℕ) :
    ((selected (d.map Int.ofNat) I).map Int.toNat).Sublist d := by
  have hs : (selected (d.map Int.ofNat) I).Sublist (d.map Int.ofNat) := by
    have hf : ((List.range (d.map Int.ofNat).length).filter (fun i => decide (i∈I))).Sublist
        (List.range (d.map Int.ofNat).length) := List.filter_sublist
    have hm := hf.map (fun i => (d.map Int.ofNat)[i]!)
    simpa only [selected,map_range_getElem] using hm
  have hn := hs.map Int.toNat
  simpa only [List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,
    List.map_id_fun',id_eq] using hn

lemma selected_nat_toNat_sum_le (d : List ℕ) (I : Finset ℕ) :
    ((selected (d.map Int.ofNat) I).map Int.toNat).sum ≤ d.sum :=
  (selected_nat_toNat_sublist d I).sum_le_sum (by intro a ha;exact Nat.zero_le _)

def splitLargeProfile (k : ℕ) (d : List ℕ) (I : Finset ℕ) : List ℕ :=
  k::(selected (d.map Int.ofNat) I).map Int.toNat

lemma splitLargeProfile_length (k : ℕ) (d : List ℕ) (I : Finset ℕ)
    (hI : I⊆Finset.range d.length) : (splitLargeProfile k d I).length=I.card+1 := by
  have hl := selected_length_card (d.map Int.ofNat) I (by simpa only [List.length_map] using hI)
  simp only [splitLargeProfile,List.length_cons,List.length_map,hl]

lemma splitLargeProfile_sum_le (k : ℕ) (d : List ℕ) (I : Finset ℕ) :
    (splitLargeProfile k d I).sum ≤ k+d.sum := by
  simpa only [splitLargeProfile,List.sum_cons] using Nat.add_le_add_left (selected_nat_toNat_sum_le d I) k

lemma normInt_splitLargeProfile (P : PsiTheory) (g k : ℕ) (d : List ℕ) (I : Finset ℕ)
    (hg : 1 ≤ g) (hI : I⊆Finset.range d.length) (Y : ℝ) (hY : Y∈Icc 0 y₀) :
    (4:ℝ)^g*normInt P g ((k:ℤ)::selected (d.map Int.ofNat) I) Y=
      W P g (I.card+1) Y*profile P g (splitLargeProfile k d I) Y := by
  have hn : ∀a∈((k:ℤ)::selected (d.map Int.ofNat) I),0 ≤ a := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · positivity
    · exact selected_nat_nonneg d I a ha
  have hlen := splitLargeProfile_length k d I hI
  unfold normInt
  rw [if_pos hn]
  simp only [List.map_cons,Int.toNat_natCast]
  change (4:ℝ)^g*normalized P g (splitLargeProfile k d I) Y=_
  rw [normalized_eq_zero_mul_profile P g _ (by rw [hlen];omega)
    (by rw [hlen];unfold Stable;omega) Y hY,hlen]
  unfold W
  ring
end WP

noncomputable section
namespace WP

def zeroIndices (d : List ℕ) : Finset ℕ :=
  (Finset.range d.length).filter (fun j => d[j]! = 0)

lemma zeroIndices_card (d : List ℕ) : (zeroIndices d).card=zeros d := by
  unfold zeroIndices
  rw [Finset.card_filter]
  exact zero_index_sum d

lemma zero_pair_subsets (d : List ℕ) :
    ((Finset.range d.length).powerset.filter (fun I => I.card=2 ∧ ∀j∈I,d[j]! = 0))=
      (zeroIndices d).powersetCard 2 := by
  classical
  ext I
  simp only [Finset.mem_filter,Finset.mem_powerset,Finset.mem_powersetCard]
  constructor
  · rintro ⟨hI,hcard,hzero⟩
    exact ⟨fun j hj => Finset.mem_filter.mpr ⟨hI hj,hzero j hj⟩,hcard⟩
  · rintro ⟨hI,hcard⟩
    refine ⟨fun j hj => (Finset.mem_filter.mp (hI hj)).1,hcard,?_⟩
    intro j hj
    exact (Finset.mem_filter.mp (hI hj)).2

lemma sum_zero_pair_subsets (d : List ℕ) :
    (∑ I ∈ (Finset.range d.length).powerset,
      if I.card=2 ∧ ∀j∈I,d[j]! = 0 then (1:ℝ) else 0)=Nat.choose (zeros d) 2 := by
  classical
  rw [←Finset.sum_filter,zero_pair_subsets]
  simp only [Finset.sum_const,Finset.card_powersetCard,zeroIndices_card,nsmul_eq_mul,mul_one]
end WP
