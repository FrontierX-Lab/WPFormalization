import Mathlib
/-! An eventually polynomial sequence with finitely many exceptions has an exact weighted sum represented by a finite algebraic recipe. Only moments through the true polynomial degree and the displayed low coefficients are used. The coefficient ring may itself be a finite-data polynomial ring. -/
noncomputable section
namespace WP.HigherOrder.BoundaryPolynomial
variable {R : Type*} [CommRing R]

def polynomialMomentRecipe (Q : Polynomial R) (M W E : ℕ → R) (D N : ℕ) : R :=
  (∑ k ∈ Finset.range (D + 1), Q.coeff k * M k) +
    ∑ l ∈ Finset.range N, W l * (E l - Q.eval (l : R))

lemma map_polynomial_eval_nat (φ : R →+* ℝ) (Q : Polynomial R) (n : ℕ) :
    (Q.map φ).eval (n : ℝ) = φ (Q.eval (n : R)) := by
  rw [Polynomial.eval_map]
  have hn : (n : ℝ) = φ (n : R) := by simp
  rw [hn, Polynomial.eval₂_at_apply]

lemma polynomialMomentRecipe_hasSum (φ : R →+* ℝ) (Q : Polynomial R) (M W E : ℕ → R)
    (D N : ℕ) (hD : Q.natDegree ≤ D) (w f : ℕ → ℝ)
    (hm : ∀ k : ℕ, k ≤ D → HasSum (fun l : ℕ => (l : ℝ) ^ k * w l) (φ (M k)))
    (hw : ∀ l : ℕ, l < N → w l = φ (W l))
    (he : ∀ l : ℕ, l < N → f l = φ (E l))
    (htail : ∀ l : ℕ, N ≤ l → f l = (Q.map φ).eval (l : ℝ)) :
    HasSum (fun l : ℕ => w l * f l) (φ (polynomialMomentRecipe Q M W E D N)) := by
  have hP : (Q.map φ).natDegree ≤ D := Polynomial.natDegree_map_le.trans hD
  have hs : HasSum (fun l : ℕ => ∑ k ∈ Finset.range (D + 1),
      φ (Q.coeff k) * ((l : ℝ) ^ k * w l))
      (∑ k ∈ Finset.range (D + 1), φ (Q.coeff k) * φ (M k)) := by
    apply hasSum_sum
    intro k hk
    exact (hm k (by have ht := Finset.mem_range.mp hk; omega)).mul_left _
  have hs' : HasSum (fun l : ℕ => w l * (Q.map φ).eval (l : ℝ))
      (∑ k ∈ Finset.range (D + 1), φ (Q.coeff k) * φ (M k)) := by
    convert! hs using 1
    funext l
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Polynomial.coeff_map]
    ring
  have hc : HasSum (fun l : ℕ => w l * (f l - (Q.map φ).eval (l : ℝ)))
      (∑ l ∈ Finset.range N, w l * (f l - (Q.map φ).eval (l : ℝ))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro l hl
    have hlN : N ≤ l := by simpa only [Finset.mem_range, not_lt] using hl
    rw [htail l hlN, sub_self, mul_zero]
  have hh := hs'.add hc
  convert! hh using 1
  · funext l
    ring
  · simp only [polynomialMomentRecipe, map_add, map_sum, map_mul, map_sub]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [hw l (Finset.mem_range.mp hl), he l (Finset.mem_range.mp hl), map_polynomial_eval_nat]
end WP.HigherOrder.BoundaryPolynomial
