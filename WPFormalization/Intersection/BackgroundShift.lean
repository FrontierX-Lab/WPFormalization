import WPFormalization.Intersection.ShiftedRecursion
/-! Exact finite reindexing when the distinguished marking merges with one
background insertion. The coordinate range is kept fixed during reindexing;
the diagonal specialization is the original `WP.backgrounds`. -/
noncomputable section
namespace WP
/-- A fixed coordinate range and cutoff for finite background reindexing. -/
def backgroundVectors (N B k : ℕ) : Finset (Fin N → ℕ) :=
  (Finset.univ.image (fun l : Fin N → Fin (B+1) => fun i => (l i).val)).filter
    (fun l => ∑ i : Fin N, (i.val+1)*l i = k)
lemma mem_backgroundVectors_iff (N B k : ℕ) (hk : k ≤ B) (l : Fin N → ℕ) :
    l ∈ backgroundVectors N B k ↔ ∑ i : Fin N, (i.val+1)*l i = k := by
  constructor
  · intro hl
    exact (Finset.mem_filter.mp hl).2
  · intro hl
    have hb (i : Fin N) : l i < B+1 := by
      have hi : (i.val+1)*l i ≤ ∑ j : Fin N, (j.val+1)*l j :=
        Finset.single_le_sum (f := fun j : Fin N => (j.val+1)*l j)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      have hh : l i ≤ (i.val+1)*l i := by nlinarith [Nat.zero_le i.val]
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨fun i => ⟨l i, hb i⟩, Finset.mem_univ _, rfl⟩, hl⟩
lemma backgroundVectors_diagonal (m : ℕ) : backgroundVectors m m m = backgrounds m := rfl
lemma background_degree_update {N : ℕ} (l : Fin N → ℕ) (i : Fin N) (s : ℕ) :
    (∑ j : Fin N, (j.val+1)*Function.update l i (l i+s) j) =
      (∑ j : Fin N, (j.val+1)*l j) + (i.val+1)*s := by
  have hsum :
      (∑ j : Fin N, (j.val+1)*Function.update l i (l i+s) j) =
        (∑ j ∈ Finset.univ.erase i, (j.val+1)*l j) + (i.val+1)*(l i+s) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hsum]
  calc
    _ = ((∑ j ∈ Finset.univ.erase i, (j.val+1)*l j)+(i.val+1)*l i)+(i.val+1)*s := by ring
    _ = _ := by rw [Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
lemma exponential_weight_succ (t : ℝ) (n : ℕ) :
    ((n+1 : ℕ) : ℝ) * (t^(n+1)/(n+1).factorial) = t*(t^n/n.factorial) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hs : ((n+1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  field_simp
  <;> ring
lemma background_weight_update {N : ℕ} (t : Fin N → ℝ) (l : Fin N → ℕ) (i : Fin N) :
    ((l i+1 : ℕ) : ℝ) *
      (∏ j : Fin N, t j^(Function.update l i (l i+1) j)/
        (Function.update l i (l i+1) j).factorial) =
    t i * (∏ j : Fin N, t j^(l j)/(l j).factorial) := by
  rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul Finset.univ (fun j => t j^(l j)/(l j).factorial) (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i, t j^(Function.update l i (l i+1) j)/
      (Function.update l i (l i+1) j).factorial) =
      ∏ j ∈ Finset.univ.erase i, t j^(l j)/(l j).factorial := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he, Function.update_self]
  have hs := exponential_weight_succ (t i) (l i)
  linear_combination (∏ j ∈ Finset.univ.erase i, t j^(l j)/(l j).factorial)*hs
end WP
namespace WP
lemma update_raise_lower {N : ℕ} (l : Fin N → ℕ) (i : Fin N) :
    Function.update (Function.update l i (l i+1)) i
      ((Function.update l i (l i+1) i)-1) = l := by
  simp
lemma update_lower_raise {N : ℕ} (l : Fin N → ℕ) (i : Fin N) (hi : 0 < l i) :
    Function.update (Function.update l i (l i-1)) i
      ((Function.update l i (l i-1) i)+1) = l := by
  simp [Nat.sub_add_cancel (by omega : 1 ≤ l i)]
lemma sum_background_raise {N B k : ℕ} (i : Fin N) (hk : k+(i.val+1) ≤ B)
    (t : Fin N → ℝ) (F : (Fin N → ℕ) → ℝ) :
    (∑ l ∈ backgroundVectors N B (k+(i.val+1)),
      (l i : ℝ)*(∏ j : Fin N, t j^(l j)/(l j).factorial)*
        F (Function.update l i (l i-1))) =
    t i * ∑ l ∈ backgroundVectors N B k,
      (∏ j : Fin N, t j^(l j)/(l j).factorial)*F l := by
  have hk' : k ≤ B := by omega
  let S := backgroundVectors N B (k+(i.val+1))
  have hfilter : (∑ l ∈ S, (l i : ℝ)*(∏ j : Fin N, t j^(l j)/(l j).factorial)*
      F (Function.update l i (l i-1))) =
      ∑ l ∈ S.filter (fun l => 0 < l i), (l i : ℝ)*(∏ j : Fin N, t j^(l j)/(l j).factorial)*
        F (Function.update l i (l i-1)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hi : 0 < l i
    · simp [hi]
    · have hz : l i = 0 := by omega
      simp [hi, hz]
  change (∑ l ∈ S, _) = _
  rw [hfilter, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun l _ => Function.update l i (l i+1))
  · intro l hl
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_backgroundVectors_iff N B _ hk _).mpr
      rw [background_degree_update,
        (mem_backgroundVectors_iff N B k hk' l).mp hl]
      simp
    · simp
  · intro l hl j hj he
    funext a
    by_cases ha : a = i
    · subst a
      have hv := congrFun he i
      simp only [Function.update_self] at hv
      omega
    · have hv := congrFun he a
      simpa [Function.update_of_ne ha] using hv
  · intro l hl
    obtain ⟨hl, hpos⟩ := Finset.mem_filter.mp hl
    let j := Function.update l i (l i-1)
    have he : Function.update j i (j i+1) = l := update_lower_raise l i hpos
    have hdeg := background_degree_update j i 1
    rw [he, (mem_backgroundVectors_iff N B _ hk l).mp hl] at hdeg
    have hj : j ∈ backgroundVectors N B k := by
      apply (mem_backgroundVectors_iff N B k hk' j).mpr
      omega
    exact ⟨j, hj, he⟩
  · intro l hl
    rw [update_raise_lower]
    simp only [Function.update_self]
    have he := background_weight_update t l i
    linear_combination -(F l)*he
end WP
