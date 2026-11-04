import WPFormalization.HigherOrder.FinitePowerSums
/-! A genuine two-variable diagonal sum has an explicit univariate polynomial of degree at most one more than the total degree. The finite binomial and Faulhaber construction works over every commutative rational algebra. -/
noncomputable section
namespace WP.HigherOrder.BoundaryPolynomial
open Polynomial
variable {R:Type*} [CommRing R] [Algebra ℚ R]
def diagonalMonomialPolynomial (R:Type*) [CommRing R] [Algebra ℚ R] (a b:ℕ):Polynomial R:=
  ∑k∈Finset.range (b+1),Polynomial.C ((Nat.choose b k:R)*(-1:R)^k)*Polynomial.X^(b-k)*
    (powerSumPolynomial R (a+k)).comp (Polynomial.X+1)
lemma diagonalMonomialPolynomial_eval (a b n:ℕ):
    (diagonalMonomialPolynomial R a b).eval (n:R)=
      ∑u∈Finset.range (n+1),(u:R)^a*((n:R)-u)^b:=by
  simp only[diagonalMonomialPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_one]
  have hn:(n:R)+1=((n+1:ℕ):R):=by push_cast;ring
  rw[hn]
  simp_rw[powerSumPolynomial_eval,Finset.mul_sum]
  rw[Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  calc
    _=(u:R)^a*(∑k∈Finset.range (b+1),(-((u:R)))^k*(n:R)^(b-k)*(Nat.choose b k:R)):=by
      rw[Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw[pow_add,neg_eq_neg_one_mul,mul_pow]
      ring
    _=(u:R)^a*((-(u:R)+(n:R))^b):=by rw[←add_pow]
    _=_:=by congr 1;ring
lemma diagonalMonomialPolynomial_degree (a b:ℕ):
    (diagonalMonomialPolynomial R a b).natDegree ≤ a+b+1:=by
  have hX:(Polynomial.X+1:Polynomial R).natDegree ≤ 1:=by
    apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le Polynomial.natDegree_X_le (by simp)
  unfold diagonalMonomialPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk':k ≤ b:=by have hh:=Finset.mem_range.mp hk;omega
  apply Polynomial.natDegree_mul_le.trans
  have hleft:(Polynomial.C ((Nat.choose b k:R)*(-1:R)^k)*Polynomial.X^(b-k)).natDegree ≤ b-k:=by
    apply Polynomial.natDegree_mul_le.trans
    rw[Polynomial.natDegree_C,zero_add]
    exact Polynomial.natDegree_X_pow_le (R:=R) (b-k)
  have hright:((powerSumPolynomial R (a+k)).comp (Polynomial.X+1)).natDegree ≤ a+k+1:=by
    apply Polynomial.natDegree_comp_le.trans
    exact (Nat.mul_le_mul (powerSumPolynomial_degree _) hX).trans_eq (Nat.mul_one _)
  omega
end WP.HigherOrder.BoundaryPolynomial

namespace WP.HigherOrder.BoundaryPolynomial
open Polynomial
variable {R:Type*} [CommRing R] [Algebra ℚ R]
def diagonalSumPolynomial (F:MvPolynomial (Fin 2) R):Polynomial R:=
  ∑m∈F.support,Polynomial.C (F.coeff m)*diagonalMonomialPolynomial R (m 0) (m 1)
lemma diagonalSumPolynomial_degree (F:MvPolynomial (Fin 2) R):
    (diagonalSumPolynomial F).natDegree ≤ F.totalDegree+1:=by
  unfold diagonalSumPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have hdeg:=MvPolynomial.le_totalDegree hm
  have hsum:m.sum (fun _ k=>k)=m 0+m 1:=by
    rw[Finsupp.sum_fintype _ _ (fun _=>rfl),Fin.sum_univ_two]
  rw[hsum] at hdeg
  apply Polynomial.natDegree_mul_le.trans
  rw[Polynomial.natDegree_C,zero_add]
  exact (diagonalMonomialPolynomial_degree _ _).trans (Nat.add_le_add_right hdeg 1)
lemma diagonalSumPolynomial_eval (F:MvPolynomial (Fin 2) R) (n:ℕ):
    (diagonalSumPolynomial F).eval (n:R)=
      ∑u∈Finset.range (n+1),MvPolynomial.eval (Fin.cases (u:R) (fun _:Fin 1=>(n:R)-u)) F:=by
  simp only[diagonalSumPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    diagonalMonomialPolynomial_eval,Finset.mul_sum]
  rw[Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw[MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m hm
  have hprod:(∏i∈m.support,(Fin.cases (u:R) (fun _:Fin 1=>(n:R)-u) i)^(m i))=
      (u:R)^(m 0)*((n:R)-u)^(m 1):=by
    let z:Fin 2→R:=Fin.cases (u:R) (fun _:Fin 1=>(n:R)-u)
    change m.prod (fun i k=>z i^k)=_
    rw[Finsupp.prod_fintype _ _ (fun _=>pow_zero _),Fin.prod_univ_two]
    have hcase:Fin.cases (u:R) (fun _:Fin 1=>(n:R)-u) (1:Fin 2)=(n:R)-u:=by
      exact Fin.cases_succ (motive:=fun _:Fin 2=>R) (zero:=(u:R)) (succ:=fun _:Fin 1=>(n:R)-u) (0:Fin 1)
    simp only[z,Fin.cases_zero,hcase]
  rw[hprod]
end WP.HigherOrder.BoundaryPolynomial
