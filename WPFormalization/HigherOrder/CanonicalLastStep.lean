import WPFormalization.HigherOrder.TriangularLocality
import WPFormalization.HigherOrder.Coherence
noncomputable section
namespace WP.HigherOrder
lemma append_last_getElem_bang (d : List ℕ) (t : ℕ) : (d ++ [t])[d.length]! = t := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append]
lemma append_prefix_getElem_bang (d : List ℕ) (t i : ℕ) (hi : i < d.length) :
    (d ++ [t])[i]! = d[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append, ite_eq_left hi]
lemma beforeCoordinate_append_last_independent (d : List ℕ) (t u i s : ℕ) (hi : i ≤ d.length) :
    beforeCoordinate (d ++ [t]) i s = beforeCoordinate (d ++ [u]) i s := by
  unfold beforeCoordinate
  simp only [List.length_append, List.length_singleton]
  congr 1
  funext j
  simp only [Fin.coe_cast]
  by_cases hj : j.val < i
  · simp only [ite_eq_left hj]
    rw [append_prefix_getElem_bang d t j.val (by omega), append_prefix_getElem_bang d u j.val (by omega)]
  · simp only [ite_eq_right hj]

lemma beforeCoordinate_append_last (d : List ℕ) (t s : ℕ) :
    beforeCoordinate (d ++ [t]) d.length s = d ++ [s] := by
  rw [beforeCoordinate_append_last_independent d t s d.length s le_rfl]
  have hn := beforeCoordinate_next (d ++ [s]) d.length (by simp)
  rw [append_last_getElem_bang] at hn
  have he := beforeCoordinate_end (d ++ [s])
  simp only [List.length_append, List.length_singleton] at he
  exact hn.trans he

lemma profileAtOrder_append_last (P : PsiTheory) (Y : ℝ) (F : HierarchyJet) (K : ℕ)
    (d : List ℕ) (t : ℕ) :
    profileAtOrder P Y F K (d ++ [t]) =
      (∑ i ∈ Finset.range d.length, ∑ s ∈ Finset.range d[i]!,
        adjacentCoefficient P Y F K i (beforeCoordinate (d ++ [0]) i s)) +
      ∑ s ∈ Finset.range t, adjacentCoefficient P Y F K d.length (d ++ [s]) := by
  unfold profileAtOrder
  simp only [List.length_append, List.length_singleton, Finset.sum_range_succ, append_last_getElem_bang]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [append_prefix_getElem_bang d t i hi']
    apply Finset.sum_congr rfl
    intro s hs
    rw [beforeCoordinate_append_last_independent d t 0 i s hi'.le]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [beforeCoordinate_append_last]

lemma profileAtOrder_append_last_step (P : PsiTheory) (Y : ℝ) (F : HierarchyJet) (K : ℕ)
    (d : List ℕ) (t : ℕ) :
    profileAtOrder P Y F K (d ++ [t + 1]) - profileAtOrder P Y F K (d ++ [t]) =
      adjacentCoefficient P Y F K d.length (d ++ [t]) := by
  rw [profileAtOrder_append_last, profileAtOrder_append_last, Finset.sum_range_succ]
  ring

lemma canonical_append_last_increment (P : PsiTheory) (Y : ℝ) (K : ℕ) (hK : 0 < K)
    (d : List ℕ) (t : ℕ) :
    profileCoefficient P Y (d ++ [t + 1]) K - profileCoefficient P Y (d ++ [t]) K =
      adjacentCoefficient P Y (formalHierarchyJet P Y) K d.length (d ++ [t]) := by
  have he₁ := formalProfile_coefficient_path_rule P Y (d ++ [t + 1]) K hK
  have he₂ := formalProfile_coefficient_path_rule P Y (d ++ [t]) K hK
  simp only [formalProfile, PowerSeries.coeff_mk] at he₁ he₂
  rw [he₁, he₂, profileAtOrder_append_last_step]
end WP.HigherOrder
