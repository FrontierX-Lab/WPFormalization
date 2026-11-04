import Mathlib
/-! The two low-coordinate boundary ranges in a diagonal sum are separated exactly once they are disjoint. The remaining small total degrees are finite exceptions. No overlap is silently discarded. -/
noncomputable section
namespace WP.HigherOrder.BoundaryPolynomial
lemma pair_boundary_split {R : Type*} [AddCommGroup R] (f : ℕ → ℕ → R) (b n : ℕ)
    (hn : 2 * b < n) (hinterior : ∀ u v : ℕ, u + v = n → b < u → b < v → f u v = 0) :
    (∑ u ∈ Finset.range (n + 1), f u (n - u)) =
      (∑ u ∈ Finset.range (b + 1), f u (n - u)) +
      ∑ v ∈ Finset.range (b + 1), f (n - v) v := by
  have hn' : n + 1 = ((b + 1) + (n - 2 * b - 1)) + (b + 1) := by omega
  rw [hn', Finset.sum_range_add, Finset.sum_range_add]
  have hmid : (∑ u ∈ Finset.range (n - 2 * b - 1), f (b + 1 + u) (n - (b + 1 + u))) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    have hu' := Finset.mem_range.mp hu
    exact hinterior _ _ (by omega) (by omega) (by omega)
  rw [hmid, add_zero]
  congr 1
  have href := Finset.sum_range_reflect (fun v => f (n - v) v) (b + 1)
  simp only [Nat.add_sub_cancel_right] at href
  calc
    _ = ∑ v ∈ Finset.range (b + 1), f (n - (b - v)) (b - v) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hv' := Finset.mem_range.mp hv
      congr 1 <;> omega
    _ = _ := href
end WP.HigherOrder.BoundaryPolynomial
