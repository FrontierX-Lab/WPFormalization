import WPFormalization.Intersection.ShiftedRecursion
/-! Dimension, sign, and stability bookkeeping for the top-degree specialization
of shifted DVV. In a separating term, total dimension compatibility forces
both factors to have top degree or at least one factor to vanish. -/
noncomputable section
namespace WP
lemma dimension_cast_of_stable (g n : ℕ) (hs : Stable g n) :
    ((dimension g n : ℕ) : ℤ) = 3*(g : ℤ)-3+n := by
  have hn : 3 ≤ 3*g+n := by unfold Stable at hs; omega
  unfold dimension
  rw [Nat.cast_sub hn]
  push_cast
  ring
lemma signed_normalized_excess (P : PsiTheory) (g : ℕ) (d : List ℤ) (Y : ℝ)
    (hd : 3*(g : ℤ)-3+d.length < d.sum) :
    (if ∀ k ∈ d, 0 ≤ k then normalized P g (d.map Int.toNat) Y else 0) = 0 := by
  by_cases hn : ∀ k ∈ d, 0 ≤ k
  · rw [if_pos hn]
    by_cases hs : Stable g d.length
    · have hm := map_ofNat_toNat d hn
      have he : (((d.map Int.toNat).sum : ℕ) : ℤ) = d.sum := by
        rw [← sum_map_int, hm]
      have hdim : dimension g (d.map Int.toNat).length < (d.map Int.toNat).sum := by
        simp only [List.length_map]
        have hcast := dimension_cast_of_stable g d.length hs
        exact_mod_cast (by omega : ((dimension g d.length : ℕ) : ℤ) < ((d.map Int.toNat).sum : ℤ))
      exact normalized_excess P g _ Y hdim
    · exact normalized_unstable P g _ Y (by simpa using hs)
  · simp [hn]
lemma weighted_excess (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hd : 3*(g : ℤ)-3+d.length < d.sum) : weighted P.psi g d = 0 := by
  have he : d.sum ≠ 3*(g : ℤ)-3+d.length := by omega
  simp [weighted, P.vanish g d (Or.inr (Or.inr he))]
lemma signed_normalized_product_top (P : PsiTheory) (g₁ g₂ : ℕ)
    (d₁ d₂ : List ℤ) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀)
    (hd : d₁.sum+d₂.sum =
      (3*(g₁ : ℤ)-3+d₁.length)+(3*(g₂ : ℤ)-3+d₂.length)) :
    (if ∀ k ∈ d₁, 0 ≤ k then normalized P g₁ (d₁.map Int.toNat) Y else 0) *
      (if ∀ k ∈ d₂, 0 ≤ k then normalized P g₂ (d₂.map Int.toNat) Y else 0) =
    weighted P.psi g₁ d₁ * weighted P.psi g₂ d₂ := by
  by_cases hdim₁ : d₁.sum = 3*(g₁ : ℤ)-3+d₁.length
  · have hdim₂ : d₂.sum = 3*(g₂ : ℤ)-3+d₂.length := by omega
    rw [signed_normalized_top P g₁ d₁ Y hY hdim₁,
      signed_normalized_top P g₂ d₂ Y hY hdim₂]
  · by_cases hgt : 3*(g₁ : ℤ)-3+d₁.length < d₁.sum
    · rw [signed_normalized_excess P g₁ d₁ Y hgt,
        weighted_excess P g₁ d₁ hgt]
      simp
    · have hgt₂ : 3*(g₂ : ℤ)-3+d₂.length < d₂.sum := by omega
      rw [signed_normalized_excess P g₂ d₂ Y hgt₂,
        weighted_excess P g₂ d₂ hgt₂]
      simp
end WP
namespace WP
lemma map_range_getElem (d : List ℤ) :
    (List.range d.length).map (fun i => d[i]!) = d := by
  apply List.ext_getElem
  · simp
  · intro i hi hd
    simp [hd]
lemma selected_partition_perm (d : List ℤ) (I : Finset ℕ) :
    (selected d I ++ selected d ((Finset.range d.length) \ I)).Perm d := by
  have hneg : ((List.range d.length).filter (fun i => i ∈ (Finset.range d.length) \ I)) =
      (List.range d.length).filter (fun i => !(decide (i ∈ I))) := by
    apply List.filter_congr
    intro i hi
    have hir : i ∈ Finset.range d.length := by simpa using hi
    simp [Finset.mem_sdiff, hir]
  have hp := (List.filter_append_perm (fun i => decide (i ∈ I))
    (List.range d.length)).map (fun i => d[i]!)
  rw [map_range_getElem] at hp
  unfold selected
  rw [hneg]
  simpa only [List.map_append] using hp
lemma selected_partition_sum (d : List ℤ) (I : Finset ℕ) :
    (selected d I).sum+(selected d ((Finset.range d.length) \ I)).sum = d.sum := by
  simpa only [List.sum_append] using (selected_partition_perm d I).sum_eq
lemma selected_partition_length (d : List ℤ) (I : Finset ℕ) :
    (selected d I).length+(selected d ((Finset.range d.length) \ I)).length = d.length := by
  simpa only [List.length_append] using (selected_partition_perm d I).length_eq
end WP

namespace WP
lemma merger_dimension (g : ℕ) (p : ℤ) (d : List ℤ)
    (hd : (p :: d).sum = 3*(g : ℤ)-3+(p :: d).length)
    (j : ℕ) (hj : j < d.length) :
    ((p+d[j]!-1) :: d.eraseIdx j).sum =
      3*(g : ℤ)-3+((p+d[j]!-1) :: d.eraseIdx j).length := by
  have hp := (List.getElem_cons_eraseIdx_perm hj).sum_eq
  have he : d[j]!+(d.eraseIdx j).sum = d.sum := by simpa [hj] using hp
  have hlen : (d.eraseIdx j).length+1 = d.length := by
    rw [List.length_eraseIdx_of_lt hj]
    omega
  simp only [List.sum_cons, List.length_cons, hlen] at hd ⊢
  omega
lemma contraction_dimension (g : ℕ) (hg : g ≠ 0) (p : ℤ) (d : List ℤ)
    (hd : (p :: d).sum = 3*(g : ℤ)-3+(p :: d).length) (u : ℕ) :
    ((u : ℤ) :: (p-2-u) :: d).sum =
      3*((g-1 : ℕ) : ℤ)-3+((u : ℤ) :: (p-2-u) :: d).length := by
  have hg' : ((g-1 : ℕ) : ℤ) = (g : ℤ)-1 := by omega
  simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, hg'] at hd ⊢
  omega
lemma separating_dimension (g g₁ : ℕ) (hg₁ : g₁ ≤ g) (p : ℤ) (d : List ℤ)
    (hd : (p :: d).sum = 3*(g : ℤ)-3+(p :: d).length) (u : ℕ) (I : Finset ℕ) :
    ((u : ℤ) :: selected d I).sum +
        ((p-2-u) :: selected d ((Finset.range d.length) \ I)).sum =
      (3*(g₁ : ℤ)-3+((u : ℤ) :: selected d I).length) +
        (3*((g-g₁ : ℕ) : ℤ)-3+((p-2-u) :: selected d ((Finset.range d.length) \ I)).length) := by
  have hs := selected_partition_sum d I
  have hl : ((selected d I).length : ℤ)+
      (selected d ((Finset.range d.length) \ I)).length = d.length := by
    exact_mod_cast selected_partition_length d I
  have hg : ((g-g₁ : ℕ) : ℤ) = (g : ℤ)-g₁ := by omega
  simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, hg] at hd ⊢
  omega
end WP
