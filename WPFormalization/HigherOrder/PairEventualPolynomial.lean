import WPFormalization.HigherOrder.DiagonalPolynomial
import WPFormalization.HigherOrder.PairBoundarySplit
import WPFormalization.HigherOrder.JointBoundaryHead
/-! A two-variable boundary-stratified sequence has an explicit eventual diagonal polynomial. Both low-coordinate corrections are retained; the identity starts strictly above twice the boundary cutoff. Summation increases the degree by at most one. The coefficient ring may itself encode finite kernel data. -/
noncomputable section
namespace WP.HigherOrder.BoundaryPolynomial
open Polynomial
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def pairValue (F : MvPolynomial (Fin 2) R) (u v : R) : R :=
  MvPolynomial.eval (Fin.cases u (fun _ : Fin 1 => v)) F

def leftSection (F : MvPolynomial (Fin 2) R) (a : R) : Polynomial R :=
  F.eval₂ Polynomial.C (Fin.cases (Polynomial.C a) (fun _ : Fin 1 => Polynomial.X))

def rightSection (F : MvPolynomial (Fin 2) R) (a : R) : Polynomial R :=
  F.eval₂ Polynomial.C (Fin.cases Polynomial.X (fun _ : Fin 1 => Polynomial.C a))

lemma leftSection_eval (F : MvPolynomial (Fin 2) R) (a v : R) :
    (leftSection F a).eval v = pairValue F a v := by
  have he := MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom v) Polynomial.C
    (Fin.cases (Polynomial.C a) (fun _ : Fin 1 => Polynomial.X)) F
  have hc : (Polynomial.evalRingHom v).comp Polynomial.C = RingHom.id R := by ext x; simp
  have hx : (fun i => Polynomial.eval v
      (Fin.cases (Polynomial.C a) (fun _ : Fin 1 => Polynomial.X) i)) =
      Fin.cases a (fun _ : Fin 1 => v) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  change Polynomial.eval v (F.eval₂ Polynomial.C (Fin.cases (Polynomial.C a) (fun _ : Fin 1 => Polynomial.X))) =
    MvPolynomial.eval₂ (RingHom.id R) (Fin.cases a (fun _ : Fin 1 => v)) F
  simpa only [Polynomial.coe_evalRingHom, hc,
    Function.comp_def, hx, MvPolynomial.eval] using he

lemma rightSection_eval (F : MvPolynomial (Fin 2) R) (a u : R) :
    (rightSection F a).eval u = pairValue F u a := by
  have he := MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom u) Polynomial.C
    (Fin.cases Polynomial.X (fun _ : Fin 1 => Polynomial.C a)) F
  have hc : (Polynomial.evalRingHom u).comp Polynomial.C = RingHom.id R := by ext x; simp
  have hx : (fun i => Polynomial.eval u
      (Fin.cases Polynomial.X (fun _ : Fin 1 => Polynomial.C a) i)) =
      Fin.cases u (fun _ : Fin 1 => a) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  change Polynomial.eval u (F.eval₂ Polynomial.C (Fin.cases Polynomial.X (fun _ : Fin 1 => Polynomial.C a))) =
    MvPolynomial.eval₂ (RingHom.id R) (Fin.cases u (fun _ : Fin 1 => a)) F
  simpa only [Polynomial.coe_evalRingHom, hc,
    Function.comp_def, hx, MvPolynomial.eval] using he

lemma leftSection_degree (F : MvPolynomial (Fin 2) R) (a : R) :
    (leftSection F a).natDegree ≤ F.totalDegree := by
  apply JointBoundary.linear_substitution_degree
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · exact Polynomial.natDegree_X_le

lemma rightSection_degree (F : MvPolynomial (Fin 2) R) (a : R) :
    (rightSection F a).natDegree ≤ F.totalDegree := by
  apply JointBoundary.linear_substitution_degree
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Polynomial.natDegree_X_le
  · simp

def pairEventualPolynomial (b : ℕ) (F : MvPolynomial (Fin 2) R)
    (L Q : ℕ → Polynomial R) : Polynomial R :=
  diagonalSumPolynomial F +
    (∑ a ∈ Finset.range (b + 1),
      (L a - leftSection F (a : R)).comp (Polynomial.X - Polynomial.C (a : R))) +
    ∑ a ∈ Finset.range (b + 1),
      (Q a - rightSection F (a : R)).comp (Polynomial.X - Polynomial.C (a : R))

lemma pairEventualPolynomial_degree (b D : ℕ) (F : MvPolynomial (Fin 2) R)
    (L Q : ℕ → Polynomial R) (hF : F.totalDegree ≤ D)
    (hL : ∀ a ≤ b, (L a).natDegree ≤ D)
    (hQ : ∀ a ≤ b, (Q a).natDegree ≤ D) :
    (pairEventualPolynomial b F L Q).natDegree ≤ D + 1 := by
  have hlin : ∀ a : ℕ, (Polynomial.X - Polynomial.C (a : R)).natDegree ≤ 1 := by
    intro a
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le Polynomial.natDegree_X_le (by simp))
  have hl : (∑ a ∈ Finset.range (b + 1),
      (L a - leftSection F (a : R)).comp (Polynomial.X - Polynomial.C (a : R))).natDegree ≤ D := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro a ha
    apply Polynomial.natDegree_comp_le.trans
    apply (Nat.mul_le_mul ((Polynomial.natDegree_sub_le _ _).trans
      (max_le (hL a (by have := Finset.mem_range.mp ha; omega))
        ((leftSection_degree _ _).trans hF))) (hlin a)).trans_eq
    exact Nat.mul_one _
  have hq : (∑ a ∈ Finset.range (b + 1),
      (Q a - rightSection F (a : R)).comp (Polynomial.X - Polynomial.C (a : R))).natDegree ≤ D := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro a ha
    apply Polynomial.natDegree_comp_le.trans
    apply (Nat.mul_le_mul ((Polynomial.natDegree_sub_le _ _).trans
      (max_le (hQ a (by have := Finset.mem_range.mp ha; omega))
        ((rightSection_degree _ _).trans hF))) (hlin a)).trans_eq
    exact Nat.mul_one _
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le _ (hq.trans (by omega))
  apply (Polynomial.natDegree_add_le _ _).trans
  exact max_le ((diagonalSumPolynomial_degree F).trans (by omega)) (hl.trans (by omega))

lemma pairEventualPolynomial_eval (b n : ℕ) (F : MvPolynomial (Fin 2) R)
    (L Q : ℕ → Polynomial R) (f : ℕ → ℕ → R) (hn : 2 * b < n)
    (hinterior : ∀ u v : ℕ, u + v = n → b < u → b < v →
      f u v = pairValue F (u : R) (v : R))
    (hleft : ∀ a ≤ b, f a (n - a) = (L a).eval ((n - a : ℕ) : R))
    (hright : ∀ a ≤ b, f (n - a) a = (Q a).eval ((n - a : ℕ) : R)) :
    (pairEventualPolynomial b F L Q).eval (n : R) =
      ∑ u ∈ Finset.range (n + 1), f u (n - u) := by
  let c : ℕ → ℕ → R := fun u v => f u v - pairValue F (u : R) (v : R)
  have hsplit := pair_boundary_split c b n hn (by
    intro u v huv hu hv
    dsimp [c]
    rw [hinterior u v huv hu hv, sub_self])
  have hdiag : (diagonalSumPolynomial F).eval (n : R) =
      ∑ u ∈ Finset.range (n + 1), pairValue F (u : R) ((n - u : ℕ) : R) := by
    rw [diagonalSumPolynomial_eval]
    apply Finset.sum_congr rfl
    intro u hu
    have hu' : u ≤ n := by have := Finset.mem_range.mp hu; omega
    rw [Nat.cast_sub hu']
    rfl
  have hl : (∑ a ∈ Finset.range (b + 1),
      (L a - leftSection F (a : R)).comp (Polynomial.X - Polynomial.C (a : R))).eval (n : R) =
      ∑ a ∈ Finset.range (b + 1), c a (n - a) := by
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≤ b := by have := Finset.mem_range.mp ha; omega
    have han : a ≤ n := by omega
    simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, leftSection_eval]
    rw [← Nat.cast_sub han, ← hleft a ha']
  have hq : (∑ a ∈ Finset.range (b + 1),
      (Q a - rightSection F (a : R)).comp (Polynomial.X - Polynomial.C (a : R))).eval (n : R) =
      ∑ a ∈ Finset.range (b + 1), c (n - a) a := by
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≤ b := by have := Finset.mem_range.mp ha; omega
    have han : a ≤ n := by omega
    simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, rightSection_eval]
    rw [← Nat.cast_sub han, ← hright a ha']
  unfold pairEventualPolynomial
  rw [Polynomial.eval_add, Polynomial.eval_add, hdiag, hl, hq, add_assoc, ← hsplit,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  dsimp [c]
  ring
end WP.HigherOrder.BoundaryPolynomial
