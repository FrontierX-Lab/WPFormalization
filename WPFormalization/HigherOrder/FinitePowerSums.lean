import Mathlib
/-! Explicit Faulhaber polynomials over an arbitrary rational algebra. Their evaluations are the genuine finite sums and their degree grows by at most one. The Bernoulli identities used here are proved in Mathlib. -/
noncomputable section
namespace WP.HigherOrder.BoundaryPolynomial
open Polynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def rationalPowerSum (p : ℕ) : Polynomial ℚ :=
  Polynomial.C ((p + 1 : ℚ)⁻¹) * (Polynomial.bernoulli (p + 1) - Polynomial.C (_root_.bernoulli (p + 1)))

def powerSumPolynomial (R : Type*) [CommRing R] [Algebra ℚ R] (p : ℕ) : Polynomial R :=
  (rationalPowerSum p).map (algebraMap ℚ R)

lemma bernoulli_natDegree_le (p : ℕ) : (Polynomial.bernoulli p).natDegree ≤ p := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_bernoulli, ite_eq_right (by omega : ¬ n ≤ p)]

lemma rationalPowerSum_degree (p : ℕ) : (rationalPowerSum p).natDegree ≤ p + 1 := by
  apply Polynomial.natDegree_mul_le.trans
  rw [Polynomial.natDegree_C, zero_add]
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (bernoulli_natDegree_le _) (by simp))

lemma rationalPowerSum_eval (p n : ℕ) :
    (rationalPowerSum p).eval (n : ℚ) = ∑ k ∈ Finset.range n, (k : ℚ) ^ p := by
  rw [rationalPowerSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_C,
    ← Polynomial.sum_range_pow_eq_bernoulli_sub n p]
  have hp : (p + 1 : ℚ) ≠ 0 := by positivity
  rw [inv_mul_cancel_left₀ hp]

lemma powerSumPolynomial_degree (p : ℕ) : (powerSumPolynomial R p).natDegree ≤ p + 1 :=
  Polynomial.natDegree_map_le.trans (rationalPowerSum_degree p)

lemma powerSumPolynomial_eval (p n : ℕ) :
    (powerSumPolynomial R p).eval (n : R) = ∑ k ∈ Finset.range n, (k : R) ^ p := by
  rw [powerSumPolynomial, Polynomial.eval_map]
  have hn : (n : R) = (algebraMap ℚ R) (n : ℚ) := by simp
  rw [hn, Polynomial.eval₂_at_apply, rationalPowerSum_eval]
  simp only [map_sum, map_pow, map_natCast]

def sumRangePolynomial (P : Polynomial R) : Polynomial R :=
  ∑ k ∈ P.support, Polynomial.C (P.coeff k) * powerSumPolynomial R k

lemma sumRangePolynomial_degree (P : Polynomial R) :
    (sumRangePolynomial P).natDegree ≤ P.natDegree + 1 := by
  unfold sumRangePolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply Polynomial.natDegree_mul_le.trans
  rw [Polynomial.natDegree_C, zero_add]
  exact (powerSumPolynomial_degree k).trans (Nat.add_le_add_right (Polynomial.le_natDegree_of_mem_supp k hk) 1)

lemma sumRangePolynomial_eval (P : Polynomial R) (n : ℕ) :
    (sumRangePolynomial P).eval (n : R) = ∑ k ∈ Finset.range n, P.eval (k : R) := by
  simp only [sumRangePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    powerSumPolynomial_eval, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_eq_sum]
  rfl
end WP.HigherOrder.BoundaryPolynomial
