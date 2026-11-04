import WPFormalization.HigherOrder.Coherence

/-! Finite telescoping along the existing canonical coordinate-increment path. -/

noncomputable section
open Set

noncomputable section
namespace WP.HigherOrder
lemma canonical_coordinate_path_sum (F : List ℕ→ℝ) (d : List ℕ) :
    (∑ i∈Finset.range d.length,∑ t∈Finset.range d[i]!,
      (F (beforeCoordinate d i (t+1))-F (beforeCoordinate d i t)))=
      F d-F (List.replicate d.length 0) := by
  calc
    _ = ∑ i∈Finset.range d.length,
        (F (beforeCoordinate d (i+1) 0)-F (beforeCoordinate d i 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_range_sub (fun t => F (beforeCoordinate d i t)) d[i]!,
        beforeCoordinate_next d i (Finset.mem_range.mp hi)]
    _ = F (beforeCoordinate d d.length 0)-F (beforeCoordinate d 0 0) :=
      Finset.sum_range_sub (fun i => F (beforeCoordinate d i 0)) d.length
    _ = _ := by rw [beforeCoordinate_end,beforeCoordinate_zero]

lemma canonical_coordinate_path_sum_reverse (F : List ℕ→ℝ) (d : List ℕ) :
    (∑ i∈Finset.range d.length,∑ t∈Finset.range d[i]!,
      (F (beforeCoordinate d i t)-F (beforeCoordinate d i (t+1))))=
      F (List.replicate d.length 0)-F d := by
  calc
    _ = -(∑ i∈Finset.range d.length,∑ t∈Finset.range d[i]!,
      (F (beforeCoordinate d i (t+1))-F (beforeCoordinate d i t))) := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = _ := by rw [canonical_coordinate_path_sum];ring
end WP.HigherOrder
