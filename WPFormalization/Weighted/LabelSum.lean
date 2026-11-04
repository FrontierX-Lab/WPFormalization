import Mathlib
/-! The exact Cauchy--Schwarz/Vandermonde label-count envelope (5.13). -/
noncomputable section
namespace WP
open Finset Finset.Nat
def weightedLabelSum (I R s : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal s, Real.sqrt (I.choose ij.1)*(R.choose ij.2 : ℝ)
lemma weightedLabelSum_cauchy (I R s : ℕ) :
    weightedLabelSum I R s ≤ Real.sqrt ((I+R).choose s)*
      Real.sqrt (∑ ij ∈ antidiagonal s, (R.choose ij.2 : ℝ)) := by
  have hv : (∑ ij ∈ antidiagonal s,
      (I.choose ij.1 : ℝ)*(R.choose ij.2 : ℝ)) = ((I+R).choose s : ℝ) := by
    have h := Nat.add_choose_eq I R s
    exact_mod_cast h.symm
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ)
    (antidiagonal s)
    (r := fun ij => Real.sqrt (I.choose ij.1)*(R.choose ij.2 : ℝ))
    (f := fun ij => (I.choose ij.1 : ℝ)*(R.choose ij.2 : ℝ))
    (g := fun ij => (R.choose ij.2 : ℝ))
    (by intro ij hij; positivity) (by intro ij hij; positivity)
    (by
      intro ij hij
      rw [mul_pow,Real.sq_sqrt (by positivity)]
      nlinarith)
  rw [hv] at hcs
  have hnon : 0 ≤ weightedLabelSum I R s := by
    unfold weightedLabelSum
    apply Finset.sum_nonneg
    intro ij hij
    positivity
  have hsum : (0 : ℝ) ≤ ∑ ij ∈ antidiagonal s, (R.choose ij.2 : ℝ) := by positivity
  have hroot : (Real.sqrt ((I+R).choose s)*Real.sqrt (∑ ij ∈ antidiagonal s, (R.choose ij.2 : ℝ)))^2 =
      ((I+R).choose s : ℝ)*(∑ ij ∈ antidiagonal s, (R.choose ij.2 : ℝ)) := by
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hsum]
  have hrootpos : 0 ≤ Real.sqrt ((I+R).choose s)*Real.sqrt (∑ ij ∈ antidiagonal s, (R.choose ij.2 : ℝ)) := by positivity
  change (weightedLabelSum I R s)^2 ≤ _ at hcs
  nlinarith
lemma weightedLabelSum_bound (I R s : ℕ) :
    weightedLabelSum I R s ≤ Real.sqrt ((I+R).choose s)*
      Real.sqrt (∑ j ∈ Finset.range (s+1), (R.choose j : ℝ)) := by
  have he : (∑ ij ∈ antidiagonal s, (R.choose ij.2 : ℝ)) =
      ∑ j ∈ Finset.range (s+1), (R.choose j : ℝ) := by
    have hs := Finset.Nat.sum_antidiagonal_swap (n := s) (f := fun ij => (R.choose ij.2 : ℝ))
    calc
      _ = ∑ ij ∈ antidiagonal s, (R.choose ij.1 : ℝ) := by simpa using hs.symm
      _ = _ := by rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa only [he] using weightedLabelSum_cauchy I R s
end WP
