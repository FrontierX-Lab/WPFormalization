import WPFormalization.Weighted.Definitions
import WPFormalization.Weighted.ModelNormalization
/-! Signed valid-model support, exact residual degree, and actual merger and
contraction normalization, including the original negative-entry zero rule. -/
noncomputable section
namespace WP
lemma validModel_residual (g : ℕ) (c : List ℤ) (m l : ℕ) (Y : ℝ)
    (hs : Stable g c.length) (hc : ∀ k ∈ c, 0 ≤ k) (hl : l ≤ m)
    (he : 3*(g : ℤ)-3+c.length-c.sum = (m : ℤ)-(l : ℤ)) :
    validModel g c Y = model g (c.map Int.toNat) Y ∧ deficit g (c.map Int.toNat) = m-l := by
  have hsum : ((c.map Int.toNat).sum : ℤ) = c.sum := by
    rw [← sum_map_int,map_ofNat_toNat c hc]
  have hdim := dimension_cast_of_stable g c.length hs
  have hle : (c.map Int.toNat).sum ≤ dimension g c.length := by omega
  have hm : deficit g (c.map Int.toNat) = m-l := by
    unfold deficit
    simp only [List.length_map]
    omega
  refine ⟨?_,hm⟩
  unfold validModel
  rw [if_pos ⟨hc,hs,by simpa only [List.length_map] using hle⟩]
lemma validModel_zero_negative (g : ℕ) (c : List ℤ) (Y : ℝ)
    (hc : ∃ k ∈ c, k < 0) : validModel g c Y = 0 := by
  unfold validModel
  apply if_neg
  intro h
  obtain ⟨k,hk,hkn⟩ := hc
  have := h.1 k hk
  omega
lemma model_pos (g : ℕ) (d : List ℕ) (Y : ℝ) (hs : Stable g d.length)
    (hY : Y ∈ Set.Icc 0 y₀) : 0 < model g d Y := by
  have hh : 0 < complexity g d.length := by unfold complexity; unfold Stable at hs; omega
  have hhR : (0 : ℝ) < complexity g d.length := by exact_mod_cast hh
  unfold model
  exact mul_pos (div_pos (mul_pos (by positivity) (Real.Gamma_pos_of_pos hhR)) (by positivity))
    (harmonicCoeff_pos Y _ _ hh hY)
lemma validModel_nonneg (g : ℕ) (c : List ℤ) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    0 ≤ validModel g c Y := by
  unfold validModel
  split_ifs with hc
  · exact (model_pos g _ Y (by simpa only [List.length_map] using hc.2.1) hY).le
  · exact le_rfl
lemma parent_deficit_cast (g : ℕ) (parent : List ℕ)
    (hs : Stable g parent.length) (hd : parent.sum ≤ dimension g parent.length) :
    (deficit g parent : ℤ) = 3*(g : ℤ)-3+parent.length-(parent.sum : ℤ) := by
  unfold deficit
  rw [Nat.cast_sub hd,dimension_cast_of_stable g parent.length hs]
lemma validModel_merger_ratio (g pivot : ℕ) (d : List ℕ) (l j : ℕ) (Y : ℝ)
    (hg : 2 ≤ g) (hd : (pivot :: d).sum ≤ dimension g (d.length+1))
    (hl : l ≤ deficit g (pivot :: d)) (hj : j < d.length)
    (hnode : 0 ≤ (pivot : ℤ)+(d[j]! : ℤ)+l-1) (hY : Y ∈ Set.Icc 0 y₀) :
    theta Y l*validModel g
      (((pivot : ℤ)+(d[j]! : ℤ)+l-1) :: (d.eraseIdx j).map Int.ofNat) Y/model g (pivot :: d) Y =
      linearQ Y (complexity g (d.length+1)) (deficit g (pivot :: d)) l /
        (3*((complexity g (d.length+1) : ℝ)-1)) := by
  let child := ((pivot : ℤ)+(d[j]! : ℤ)+l-1) :: (d.eraseIdx j).map Int.ofNat
  have hlen : child.length = d.length := by
    dsimp only [child]
    simp only [List.length_cons,List.length_map,List.length_eraseIdx_of_lt hj]
    omega
  have hc : ∀ k ∈ child, 0 ≤ k := by
    intro k hk
    rcases List.mem_cons.mp hk with hk | hk
    · subst k; exact hnode
    · obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hk
      exact Int.natCast_nonneg _
  have hsum : child.sum = ((pivot :: d).sum : ℤ)+(l : ℤ)-1 := by
    have hp := (List.getElem_cons_eraseIdx_perm hj).sum_eq
    have hpR : (d[j]! : ℤ)+((d.eraseIdx j).sum : ℤ) = (d.sum : ℤ) := by
      exact_mod_cast (by simpa [hj] using hp)
    dsimp only [child]
    rw [List.sum_cons,sum_map_int]
    simp only [List.sum_cons,Nat.cast_add]
    omega
  have hs : Stable g child.length := by unfold Stable; omega
  have hspar : Stable g (pivot :: d).length := by unfold Stable; omega
  have hres : 3*(g : ℤ)-3+child.length-child.sum =
      (deficit g (pivot :: d) : ℤ)-(l : ℤ) := by
    rw [hlen,hsum,parent_deficit_cast g (pivot :: d) hspar (by simpa only [List.length_cons] using hd)]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring
  have hvalid := validModel_residual g child (deficit g (pivot :: d)) l Y hs hc hl hres
  rw [hvalid.1]
  apply model_merger_ratio g (pivot :: d) (child.map Int.toNat) l Y
  · simp only [List.length_cons]; unfold complexity; omega
  · simp only [List.length_map,List.length_cons,hlen]; unfold complexity; omega
  · exact hvalid.2
  · exact hY
lemma validModel_contraction_ratio (g pivot : ℕ) (d : List ℕ) (l u : ℕ) (Y : ℝ)
    (hg : 2 ≤ g) (hd : (pivot :: d).sum ≤ dimension g (d.length+1))
    (hl : l ≤ deficit g (pivot :: d)) (hu : u ∈ Finset.range (pivot+l-1))
    (hY : Y ∈ Set.Icc 0 y₀) :
    theta Y l*validModel (g-1)
      ((u : ℤ) :: ((pivot : ℤ)+l-2-u) :: d.map Int.ofNat) Y/model g (pivot :: d) Y =
      4*linearQ Y (complexity g (d.length+1)) (deficit g (pivot :: d)) l /
        (3*((complexity g (d.length+1) : ℝ)-1)) := by
  let child := (u : ℤ) :: ((pivot : ℤ)+l-2-u) :: d.map Int.ofNat
  have hu' := Finset.mem_range.mp hu
  have hlen : child.length = d.length+2 := by simp [child]
  have hc : ∀ k ∈ child, 0 ≤ k := by
    intro k hk
    rcases List.mem_cons.mp hk with hk | hk
    · subst k; positivity
    · rcases List.mem_cons.mp hk with hk | hk
      · subst k; omega
      · obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hk
        exact Int.natCast_nonneg _
  have hsum : child.sum = ((pivot :: d).sum : ℤ)+(l : ℤ)-2 := by
    dsimp only [child]
    rw [List.sum_cons,List.sum_cons,sum_map_int]
    simp only [List.sum_cons,Nat.cast_add]
    ring
  have hs : Stable (g-1) child.length := by rw [hlen]; unfold Stable; omega
  have hspar : Stable g (pivot :: d).length := by unfold Stable; omega
  have hres : 3*((g-1 : ℕ) : ℤ)-3+child.length-child.sum =
      (deficit g (pivot :: d) : ℤ)-(l : ℤ) := by
    rw [hlen,hsum,parent_deficit_cast g (pivot :: d) hspar (by simpa only [List.length_cons] using hd)]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    have hcast : ((g-1 : ℕ) : ℤ) = (g : ℤ)-1 := by omega
    rw [hcast]
    ring
  have hvalid := validModel_residual (g-1) child (deficit g (pivot :: d)) l Y hs hc hl hres
  rw [hvalid.1]
  apply model_contraction_ratio g (pivot :: d) (child.map Int.toNat) l Y (by omega)
  · simp only [List.length_cons]; unfold complexity; omega
  · simp only [List.length_map,List.length_cons,hlen]; unfold complexity; omega
  · exact hvalid.2
  · exact hY
end WP
