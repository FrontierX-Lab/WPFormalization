import WPFormalization.HigherOrder.Triangular
/-! Exact finite tuples for merger labels. Removing a list coordinate agrees with Fin.succAbove, and the pivot/target affine head is represented by its genuine nonnegative integer coefficient mask. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
lemma eraseIdx_ofFn_eq {q : ℕ} (d : Fin (q + 1) → ℕ) (j : Fin (q + 1)) :
    List.ofFn (fun i : Fin q => d (j.succAbove i)) = (List.ofFn d).eraseIdx j.val := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_eraseIdx]
    simp only [j.isLt, ite_true]
    omega
  · intro k h₁ h₂
    rw [List.getElem_ofFn, List.getElem_eraseIdx]
    have hq : k < q := by simpa only [List.length_ofFn] using h₁
    by_cases hk : k < j.val
    · simp only [dite_eq_left hk, List.getElem_ofFn]
      congr 1
      apply Fin.ext
      change (j.succAbove ⟨k, hq⟩).val = k
      rw [Fin.succAbove_of_castSucc_lt j ⟨k, hq⟩ (by exact hk)]
      rfl
    · simp only [dite_eq_right hk, List.getElem_ofFn]
      congr 1
      apply Fin.ext
      change (j.succAbove ⟨k, hq⟩).val = k + 1
      rw [Fin.succAbove_of_le_castSucc j ⟨k, hq⟩ (by exact Nat.le_of_not_gt hk)]
      rfl
end WP.HigherOrder.JointBoundary

namespace WP.HigherOrder.JointBoundary

def mergerHeadCoefficients {q : ℕ} (j : Fin (q + 1)) : Fin (q + 2) → ℕ :=
  Fin.cases 1 (fun k => if k = j then 1 else 0)

def mergerRemainingIndex {q : ℕ} (j : Fin (q + 1)) : Fin q → Fin (q + 2) :=
  fun i => (j.succAbove i).succ

lemma mergerHeadCoefficients_sum {q : ℕ} (j : Fin (q + 1)) (d : Fin (q + 2) → ℕ) :
    (∑ i : Fin (q + 2), mergerHeadCoefficients j i * d i) = d 0 + d j.succ := by
  rw [Fin.sum_univ_succ]
  simp [mergerHeadCoefficients, ite_mul]
end WP.HigherOrder.JointBoundary
