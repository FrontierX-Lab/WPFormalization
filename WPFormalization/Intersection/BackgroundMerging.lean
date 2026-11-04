import WPFormalization.Intersection.BackgroundAmplitude
/-! Background marking mergers in the exact shifted DVV equation. This counts
identical insertions, proves the erase permutations and double-factorial
cancellation, and then derives the full weighted background-merging operator. -/
noncomputable section
namespace WP
lemma background_count {N : ℕ} (l : Fin N → ℕ) (a : ℕ) :
    (backgroundDegrees l).count a = ∑ i, if i.val+2 = a then l i else 0 := by
  simp [backgroundDegrees, List.count_flatMap, List.count_replicate, List.finRange, List.sum_ofFn]
lemma background_count_at {N : ℕ} (l : Fin N → ℕ) (i : Fin N) :
    (backgroundDegrees l).count (i.val+2) = l i := by
  rw [background_count]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have he : j.val+2 ≠ i.val+2 := by
      intro hh
      apply hji
      apply Fin.ext
      omega
    simp only [if_neg he]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))
lemma background_cons_update_perm {N : ℕ} (l : Fin N → ℕ) (i : Fin N)
    (hi : 0 < l i) :
    ((i.val+2) :: backgroundDegrees (Function.update l i (l i-1))).Perm (backgroundDegrees l) := by
  apply List.perm_iff_count.mpr
  intro a
  by_cases ha : i.val+2 = a
  · subst a
    simp only [List.count_cons_self, background_count_at, Function.update_self]
    omega
  · rw [List.count_cons]
    simp only [beq_iff_eq, ha, Bool.false_eq_true, ite_false, add_zero]
    rw [background_count, background_count]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases he : j = i
    · subst j
      simp [ha]
    · rw [Function.update_of_ne he]
lemma sum_map_background {N : ℕ} (l : Fin N → ℕ) (G : ℕ → ℝ) :
    ((backgroundDegrees l).map G).sum = ∑ i, (l i : ℝ)*G (i.val+2) := by
  simp [backgroundDegrees, List.map_flatMap, List.flatMap_def, List.sum_flatten,
    List.map_map, List.finRange, List.sum_ofFn, nsmul_eq_mul]
end WP
namespace WP
lemma sum_range_getElem {α : Type*} [Inhabited α] (d : List α) (G : α → ℝ) :
    (∑ j ∈ Finset.range d.length, G d[j]!) = (d.map G).sum := by
  induction d with
  | nil => simp
  | cons a d ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    rw [Finset.sum_range_succ']
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [ih]
    ring
lemma oddFactorial_pos (n : ℕ) : 0 < oddFactorial n := by
  unfold oddFactorial
  apply Finset.prod_pos
  intro j hj
  omega
lemma doubleWeight_cons (k : ℤ) (d : List ℤ) :
    doubleWeight (k :: d) = (oddFactorial k.toNat : ℝ)*doubleWeight d := rfl
lemma doubleWeight_append (d e : List ℤ) :
    doubleWeight (d++e) = doubleWeight d*doubleWeight e := by
  simp [doubleWeight, List.map_append, List.prod_append]
lemma doubleWeight_pos (d : List ℤ) : 0 < doubleWeight d := by
  unfold doubleWeight
  apply List.prod_pos
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  exact_mod_cast oddFactorial_pos k.toNat
lemma doubleWeight_perm {d e : List ℤ} (h : d.Perm e) : doubleWeight d = doubleWeight e := by
  unfold doubleWeight
  exact (h.map (fun k : ℤ => (oddFactorial k.toNat : ℝ))).prod_eq
lemma weighted_perm (P : PsiTheory) (g : ℕ) {d e : List ℤ} (h : d.Perm e) :
    weighted P.psi g d = weighted P.psi g e := by
  unfold weighted
  rw [doubleWeight_perm h, P.symmetry g d e h]
lemma doubleWeight_background_update {N : ℕ} (l : Fin N → ℕ) (i : Fin N)
    (hi : 0 < l i) : doubleWeight ((backgroundDegrees l).map Int.ofNat) =
      (oddFactorial (i.val+2) : ℝ)*
        doubleWeight ((backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat) := by
  have he := doubleWeight_perm ((background_cons_update_perm l i hi).map Int.ofNat)
  simpa only [List.map_cons, doubleWeight_cons, Int.ofNat_eq_natCast, Int.toNat_natCast] using he.symm
lemma background_merge_weight {N : ℕ} (l : Fin N → ℕ) (i : Fin N)
    (hi : 0 < l i) :
    (((2*(i.val+2)+1 : ℕ) : ℝ)*
      doubleWeight ((backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat)) /
      doubleWeight ((backgroundDegrees l).map Int.ofNat) = 1/(oddFactorial (i.val+1) : ℝ) := by
  rw [doubleWeight_background_update l i hi]
  have ho : (oddFactorial (i.val+2) : ℝ) =
      (((2*(i.val+2)+1 : ℕ) : ℝ)*(oddFactorial (i.val+1) : ℝ)) := by
    rw [show i.val+2 = (i.val+1)+1 by omega, oddFactorial_succ]
    push_cast
    ring
  rw [ho]
  have hb := (doubleWeight_pos ((backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat)).ne'
  have hh : (oddFactorial (i.val+1) : ℝ) ≠ 0 := by exact_mod_cast (oddFactorial_pos (i.val+1)).ne'
  field_simp [hb, hh]
  <;> ring
end WP
namespace WP
lemma doubleWeight_background {N : ℕ} (l : Fin N → ℕ) :
    doubleWeight ((backgroundDegrees l).map Int.ofNat) =
      ∏ i, (oddFactorial (i.val+2) : ℝ)^(l i) := by
  simp [doubleWeight, backgroundDegrees, List.flatMap_def, List.map_flatten,
    List.prod_flatten, List.map_map, List.finRange, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [show ((i.val : ℤ)+2).toNat = i.val+2 by omega]
lemma doubleWeight_background_split {N : ℕ} (l j : Fin N → ℕ)
    (hj : ∀ i, j i ≤ l i) :
    doubleWeight ((backgroundDegrees j).map Int.ofNat)*
      doubleWeight ((backgroundDegrees (fun i => l i-j i)).map Int.ofNat) =
      doubleWeight ((backgroundDegrees l).map Int.ofNat) := by
  rw [doubleWeight_background, doubleWeight_background, doubleWeight_background,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_add, Nat.add_sub_of_le (hj i)]
lemma weighted_append_cancel (P : PsiTheory) (g : ℕ) (d e : List ℤ) :
    weighted P.psi g (d++e)/doubleWeight e = doubleWeight d*P.psi g (d++e) := by
  unfold weighted
  rw [doubleWeight_append]
  field_simp [(doubleWeight_pos e).ne']
lemma weighted_background_split_cancel (P : PsiTheory) (g₁ g₂ : ℕ) (d₁ d₂ : List ℤ)
    {N : ℕ} (l j : Fin N → ℕ) (hj : ∀ i, j i ≤ l i) :
    (weighted P.psi g₁ (d₁ ++ (backgroundDegrees j).map Int.ofNat)*
      weighted P.psi g₂ (d₂ ++ (backgroundDegrees (fun i => l i-j i)).map Int.ofNat)) /
      doubleWeight ((backgroundDegrees l).map Int.ofNat) =
    (doubleWeight d₁*P.psi g₁ (d₁ ++ (backgroundDegrees j).map Int.ofNat))*
      (doubleWeight d₂*P.psi g₂ (d₂ ++ (backgroundDegrees (fun i => l i-j i)).map Int.ofNat)) := by
  unfold weighted
  rw [doubleWeight_append, doubleWeight_append,
    ← doubleWeight_background_split l j hj]
  field_simp [(doubleWeight_pos ((backgroundDegrees j).map Int.ofNat)).ne',
    (doubleWeight_pos ((backgroundDegrees (fun i => l i-j i)).map Int.ofNat)).ne']
  <;> ring
lemma weighted_background_merge_cancel (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (l : Fin N → ℕ) (i : Fin N) (hi : 0 < l i) :
    (((2*(i.val+2)+1 : ℕ) : ℝ)*
      weighted P.psi g (d ++ (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat)) /
      doubleWeight ((backgroundDegrees l).map Int.ofNat) =
    1/(oddFactorial (i.val+1) : ℝ)*doubleWeight d*
      P.psi g (d ++ (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat) := by
  unfold weighted
  rw [doubleWeight_append]
  have he := background_merge_weight l i hi
  linear_combination (doubleWeight d*P.psi g
    (d ++ (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat))*he
end WP
namespace WP
lemma mem_backgroundDegrees {N : ℕ} (l : Fin N → ℕ) (k : ℕ) :
    k ∈ backgroundDegrees l ↔ ∃ i : Fin N, l i ≠ 0 ∧ k = i.val+2 := by
  simp [backgroundDegrees, List.mem_flatMap, List.mem_replicate]
lemma background_erase_perm {N : ℕ} (l : Fin N → ℕ) (j : ℕ)
    (hj : j < (backgroundDegrees l).length) (i : Fin N)
    (hi : (backgroundDegrees l)[j]! = i.val+2) (hli : 0 < l i) :
    ((backgroundDegrees l).eraseIdx j).Perm
      (backgroundDegrees (Function.update l i (l i-1))) := by
  have hp := List.getElem_cons_eraseIdx_perm hj
  have hget : (backgroundDegrees l)[j] = i.val+2 := by simpa [hj] using hi
  rw [hget] at hp
  exact (hp.trans (background_cons_update_perm l i hli).symm).cons_inv
lemma sum_background_mergers (P : PsiTheory) (g : ℕ) (p : ℤ) (d : List ℤ)
    {N : ℕ} (l : Fin N → ℕ) :
    (∑ j ∈ Finset.range (backgroundDegrees l).length,
      (((2*(backgroundDegrees l)[j]!+1 : ℕ) : ℝ))*
        weighted P.psi g (((p+(backgroundDegrees l)[j]!-1) :: d) ++
          ((backgroundDegrees l).eraseIdx j).map Int.ofNat)) =
    ∑ i : Fin N, (l i : ℝ)*(((2*(i.val+2)+1 : ℕ) : ℝ)*
      weighted P.psi g (((p+(i.val+2)-1) :: d) ++
        (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat)) := by
  let G : ℕ → ℝ := fun k => if h : k-2 < N then
    (((2*k+1 : ℕ) : ℝ))*weighted P.psi g (((p+k-1) :: d) ++
      (backgroundDegrees (Function.update l ⟨k-2, h⟩ (l ⟨k-2, h⟩-1))).map Int.ofNat) else 0
  have hG (i : Fin N) : G (i.val+2) = (((2*(i.val+2)+1 : ℕ) : ℝ))*
      weighted P.psi g (((p+(i.val+2)-1) :: d) ++
        (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat) := by
    simp [G, i.isLt]
  calc
    _ = ∑ j ∈ Finset.range (backgroundDegrees l).length, G (backgroundDegrees l)[j]! := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hmem : (backgroundDegrees l)[j]! ∈ backgroundDegrees l := by
        simpa [hj'] using (List.getElem_mem (l := backgroundDegrees l) j hj')
      obtain ⟨i, hli, hi⟩ := (mem_backgroundDegrees l _).mp hmem
      rw [hi, hG i]
      congr 1
      apply weighted_perm P g
      exact (List.Perm.refl ((p+(i.val+2)-1) :: d)).append
        ((background_erase_perm l j hj' i hi (Nat.pos_of_ne_zero hli)).map Int.ofNat)
    _ = ((backgroundDegrees l).map G).sum := sum_range_getElem _ G
    _ = ∑ i : Fin N, (l i : ℝ)*G (i.val+2) := sum_map_background l G
    _ = _ := by simp only [hG]
end WP
namespace WP
lemma sum_background_mergers_cancel (P : PsiTheory) (g : ℕ) (p : ℤ) (d : List ℤ)
    {N : ℕ} (l : Fin N → ℕ) :
    (∑ j ∈ Finset.range (backgroundDegrees l).length,
      (((2*(backgroundDegrees l)[j]!+1 : ℕ) : ℝ))*
        weighted P.psi g (((p+(backgroundDegrees l)[j]!-1) :: d) ++
          ((backgroundDegrees l).eraseIdx j).map Int.ofNat)) /
        doubleWeight ((backgroundDegrees l).map Int.ofNat) =
    ∑ i : Fin N, (l i : ℝ)*(1/(oddFactorial (i.val+1) : ℝ)*
      doubleWeight ((p+(i.val+2)-1) :: d)*P.psi g (((p+(i.val+2)-1) :: d) ++
        (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat)) := by
  rw [sum_background_mergers, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hli : l i = 0
  · simp [hli]
  · have hpos : 0 < l i := Nat.pos_of_ne_zero hli
    calc
      _ = (l i : ℝ)*((((2*(i.val+2)+1 : ℕ) : ℝ)*
          weighted P.psi g (((p+(i.val+2)-1) :: d) ++
            (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat)) /
          doubleWeight ((backgroundDegrees l).map Int.ofNat)) := by ring
      _ = _ := by rw [weighted_background_merge_cancel P g _ l i hpos]
lemma background_merging_operator (P : PsiTheory) (g : ℕ) (p : ℤ) (d : List ℤ)
    {N : ℕ} (B k : ℕ) (hk : k ≤ B) (t : Fin N → ℝ) :
    (∑ l ∈ backgroundVectors N B k, (∏ i, t i^(l i)/(l i).factorial)*
      ((∑ j ∈ Finset.range (backgroundDegrees l).length,
        (((2*(backgroundDegrees l)[j]!+1 : ℕ) : ℝ))*
          weighted P.psi g (((p+(backgroundDegrees l)[j]!-1) :: d) ++
            ((backgroundDegrees l).eraseIdx j).map Int.ofNat)) /
          doubleWeight ((backgroundDegrees l).map Int.ofNat))) =
    ∑ i : Fin N, if i.val+1 ≤ k then t i/(oddFactorial (i.val+1) : ℝ)*
      finiteBackgroundAmplitude P g ((p+(i.val+2)-1) :: d) B (k-(i.val+1)) t else 0 := by
  simp_rw [sum_background_mergers_cancel]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hwi : i.val+1 ≤ k
  · rw [if_pos hwi]
    let F : (Fin N → ℕ) → ℝ := fun l =>
      doubleWeight ((p+(i.val+2)-1) :: d)*P.psi g (((p+(i.val+2)-1) :: d) ++
        (backgroundDegrees l).map Int.ofNat)
    have hsum := sum_background_raise i (show k-(i.val+1)+(i.val+1) ≤ B by omega) t F
    rw [Nat.sub_add_cancel hwi] at hsum
    have hbase : (∑ l ∈ backgroundVectors N B (k-(i.val+1)),
        (∏ j, t j^(l j)/(l j).factorial)*F l) =
        finiteBackgroundAmplitude P g ((p+(i.val+2)-1) :: d) B (k-(i.val+1)) t := by
      unfold finiteBackgroundAmplitude
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      dsimp only [F]
      ring
    calc
      _ = 1/(oddFactorial (i.val+1) : ℝ)*
          (∑ l ∈ backgroundVectors N B k, (l i : ℝ)*
            (∏ j, t j^(l j)/(l j).factorial)*F (Function.update l i (l i-1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        dsimp only [F]
        ring
      _ = 1/(oddFactorial (i.val+1) : ℝ)*(t i*
          (∑ l ∈ backgroundVectors N B (k-(i.val+1)),
            (∏ j, t j^(l j)/(l j).factorial)*F l)) := by rw [hsum]
      _ = _ := by rw [hbase]; ring
  · rw [if_neg hwi]
    apply Finset.sum_eq_zero
    intro l hl
    have hz := background_zero_of_ge hk l hl i (by omega : k ≤ i.val)
    simp [hz]
end WP
