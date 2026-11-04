import WPFormalization.HigherOrder.FinitePowerSums
import WPFormalization.HigherOrder.JointBoundaryPair
/-! Finite first-coordinate summation is a literal multivariate Faulhaber polynomial, retaining every other variable and increasing total degree by at most one. The coefficient ring can itself contain finite kernel-data polynomials. -/
noncomputable section
namespace WP.HigherOrder.BoundaryPolynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def polynomialInVariable {ι : Type*} (i : ι) (P : Polynomial R) : MvPolynomial ι R :=
  P.eval₂ MvPolynomial.C (MvPolynomial.X i)

lemma polynomialInVariable_degree {ι : Type*} (i : ι) (P : Polynomial R) :
    (polynomialInVariable i P).totalDegree ≤ P.natDegree := by
  rw [polynomialInVariable, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro n hn
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  have hX : (MvPolynomial.X i : MvPolynomial ι R).totalDegree ≤ 1 := by
    change (MvPolynomial.monomial (Finsupp.single i 1) (1 : R)).totalDegree ≤ 1
    simpa using (MvPolynomial.totalDegree_monomial_le (Finsupp.single i 1) (1 : R))
  exact (MvPolynomial.totalDegree_pow _ _).trans
    ((Nat.mul_le_mul_left n hX).trans (by simpa using Polynomial.le_natDegree_of_mem_supp n hn))

lemma polynomialInVariable_eval {ι : Type*} (i : ι) (P : Polynomial R) (x : ι → R) :
    MvPolynomial.eval x (polynomialInVariable i P) = P.eval (x i) := by
  simp only [polynomialInVariable, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    map_sum, map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Polynomial.eval, RingHom.id_apply]

def firstVariableSumPolynomial {p : ℕ} (F : MvPolynomial (Fin (p + 1)) R) :
    MvPolynomial (Fin (p + 1)) R :=
  ∑ m ∈ F.support, MvPolynomial.C (F.coeff m) *
    polynomialInVariable 0 (powerSumPolynomial R (m 0)) *
      ∏ i : Fin p, MvPolynomial.X i.succ ^ m i.succ

lemma firstVariableSumPolynomial_degree {p : ℕ} (F : MvPolynomial (Fin (p + 1)) R) :
    (firstVariableSumPolynomial F).totalDegree ≤ F.totalDegree + 1 := by
  unfold firstVariableSumPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  have hsum : m.sum (fun _ k => k) = m 0 + ∑ i : Fin p, m i.succ := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ]
  have hdeg := MvPolynomial.le_totalDegree hm
  rw [hsum] at hdeg
  have hhead : (MvPolynomial.C (F.coeff m) *
      polynomialInVariable (0 : Fin (p + 1)) (powerSumPolynomial R (m 0))).totalDegree ≤ m 0 + 1 := by
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact (polynomialInVariable_degree _ _).trans (powerSumPolynomial_degree _)
  have htail : (∏ i : Fin p, MvPolynomial.X i.succ ^ m i.succ : MvPolynomial (Fin (p + 1)) R).totalDegree ≤
      ∑ i : Fin p, m i.succ := by
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    have hX : (MvPolynomial.X i.succ : MvPolynomial (Fin (p + 1)) R).totalDegree ≤ 1 := by
      change (MvPolynomial.monomial (Finsupp.single i.succ 1) (1 : R)).totalDegree ≤ 1
      simpa using (MvPolynomial.totalDegree_monomial_le (Finsupp.single i.succ 1) (1 : R))
    exact (MvPolynomial.totalDegree_pow _ _).trans (by nlinarith)
  exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

lemma firstVariableSumPolynomial_eval {p : ℕ} (F : MvPolynomial (Fin (p + 1)) R)
    (n : ℕ) (tail : Fin p → R) :
    MvPolynomial.eval (Fin.cases (n : R) tail) (firstVariableSumPolynomial F) =
      ∑ t ∈ Finset.range n, MvPolynomial.eval (Fin.cases (t : R) tail) F := by
  simp only [firstVariableSumPolynomial, map_sum, map_mul, polynomialInVariable_eval,
    MvPolynomial.eval_C, map_prod, map_pow, MvPolynomial.eval_X, Fin.cases_zero,
    Fin.cases_succ, powerSumPolynomial_eval]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro m hm
  rw [Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  ring
end WP.HigherOrder.BoundaryPolynomial
