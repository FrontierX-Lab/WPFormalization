import WPFormalization.Intersection.BackgroundShift
/-! Exact zero extension between the original degree-bounded multiplicity
vectors and a fixed ambient coordinate range. Both the background insertion
list and exponential weight are preserved by this finite reindexing. -/
noncomputable section
namespace WP
/-- Extend a background multiplicity vector by zero on the additional coordinates. -/
def zeroExtendBackground {k : ℕ} (s : ℕ) (l : Fin k → ℕ) : Fin (k+s) → ℕ :=
  fun i => if h : i.val < k then l ⟨i.val, h⟩ else 0
lemma background_degree_zeroExtend {k : ℕ} (s : ℕ) (l : Fin k → ℕ) :
    (∑ i : Fin (k+s), (i.val+1)*zeroExtendBackground s l i) =
      ∑ i : Fin k, (i.val+1)*l i := by
  rw [Fin.sum_univ_add]
  have hl : (∑ i : Fin k, ((Fin.castAdd s i).val+1)*
      zeroExtendBackground s l (Fin.castAdd s i)) = ∑ i : Fin k, (i.val+1)*l i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [zeroExtendBackground]
  have hr : (∑ i : Fin s, ((Fin.natAdd k i).val+1)*
      zeroExtendBackground s l (Fin.natAdd k i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [zeroExtendBackground, show ¬k+i.val < k by omega]
  rw [hl, hr, add_zero]
lemma background_zero_of_ge {N B k : ℕ} (hk : k ≤ B)
    (l : Fin N → ℕ) (hl : l ∈ backgroundVectors N B k)
    (i : Fin N) (hi : k ≤ i.val) : l i = 0 := by
  have hd := (mem_backgroundVectors_iff N B k hk l).mp hl
  have hs : (i.val+1)*l i ≤ ∑ j : Fin N, (j.val+1)*l j :=
    Finset.single_le_sum (f := fun j : Fin N => (j.val+1)*l j)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  by_contra he
  have hp : 1 ≤ l i := by omega
  nlinarith
lemma backgroundDegrees_truncate {k : ℕ} (N : ℕ) (l : Fin k → ℕ) (hk : k ≤ N) :
    backgroundDegrees (fun i : Fin N => if h : i.val < k then l ⟨i.val, h⟩ else 0) =
      backgroundDegrees l := by
  induction N with
  | zero =>
    have he : k = 0 := by omega
    subst k
    simp [backgroundDegrees]
  | succ N ih =>
    by_cases he : k = N+1
    · subst k
      have hf : (fun i : Fin (N+1) => if h : i.val < N+1 then l ⟨i.val, h⟩ else 0) = l := by
        funext i
        simp only [dif_pos i.isLt]
      rw [hf]
    · have hk' : k ≤ N := by omega
      have hn : ¬N < k := by omega
      unfold backgroundDegrees
      rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
      simp only [List.flatMap_cons, List.flatMap_nil, Fin.val_last,
        dif_neg hn, List.replicate_zero, List.append_nil]
      change backgroundDegrees (fun i : Fin N => if h : i.val < k then l ⟨i.val, h⟩ else 0) =
        backgroundDegrees l
      exact ih hk'
lemma backgroundDegrees_zeroExtend {k : ℕ} (s : ℕ) (l : Fin k → ℕ) :
    backgroundDegrees (zeroExtendBackground s l) = backgroundDegrees l :=
  backgroundDegrees_truncate (k+s) l (Nat.le_add_right k s)
lemma background_weight_zeroExtend {k : ℕ} (s : ℕ) (l : Fin k → ℕ)
    (t : Fin (k+s) → ℝ) :
    (∏ i : Fin (k+s), t i^(zeroExtendBackground s l i)/
      (zeroExtendBackground s l i).factorial) =
    ∏ i : Fin k, t (Fin.castAdd s i)^(l i)/(l i).factorial := by
  rw [Fin.prod_univ_add]
  have hl : (∏ i : Fin k, t (Fin.castAdd s i)^(zeroExtendBackground s l (Fin.castAdd s i))/
      (zeroExtendBackground s l (Fin.castAdd s i)).factorial) =
      ∏ i : Fin k, t (Fin.castAdd s i)^(l i)/(l i).factorial := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [zeroExtendBackground]
  have hr : (∏ i : Fin s, t (Fin.natAdd k i)^(zeroExtendBackground s l (Fin.natAdd k i))/
      (zeroExtendBackground s l (Fin.natAdd k i)).factorial) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    simp [zeroExtendBackground, show ¬k+i.val < k by omega]
  rw [hl, hr, mul_one]
lemma sum_backgroundVectors_zeroExtend (k s B : ℕ) (hk : k ≤ B)
    (F : (Fin (k+s) → ℕ) → ℝ) :
    (∑ l ∈ backgroundVectors (k+s) B k, F l) =
      ∑ l ∈ backgrounds k, F (zeroExtendBackground s l) := by
  symm
  apply Finset.sum_bij (fun l _ => zeroExtendBackground s l)
  · intro l hl
    apply (mem_backgroundVectors_iff (k+s) B k hk _).mpr
    rw [background_degree_zeroExtend, (mem_backgrounds_iff k l).mp hl]
  · intro l hl j hj he
    funext i
    have hi := congrFun he (Fin.castAdd s i)
    simpa [zeroExtendBackground] using hi
  · intro l hl
    let j : Fin k → ℕ := fun i => l (Fin.castAdd s i)
    have he : zeroExtendBackground s j = l := by
      funext i
      by_cases hi : i.val < k
      · have hcast : Fin.castAdd s (⟨i.val, hi⟩ : Fin k) = i := by apply Fin.ext; rfl
        simp [zeroExtendBackground, hi, j, hcast]
      · have hz : l i = 0 := background_zero_of_ge hk l hl i (by omega)
        simp [zeroExtendBackground, hi, hz]
    have hj : j ∈ backgrounds k := by
      apply (mem_backgrounds_iff k j).mpr
      rw [← background_degree_zeroExtend s j, he]
      exact (mem_backgroundVectors_iff (k+s) B k hk l).mp hl
    exact ⟨j, hj, he⟩
  · intro l hl
    rfl
end WP
