import WPFormalization.HigherOrder.JointDiagonalPolynomial
/-! Joint eventual diagonal polynomials retain both low-coordinate boundary corrections. The identity applies strictly above total 2b and preserves all remaining variables. The degree bound is D+1; no overlap is discarded at small totals. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]
def pairSlot {p : ℕ} (u v : MvPolynomial (Fin (p + 1)) R)
    (F : MvPolynomial (Fin (p + 2)) R) : MvPolynomial (Fin (p + 1)) R :=
  F.eval₂ MvPolynomial.C
    (Fin.cases u (Fin.cases v (fun j => MvPolynomial.X j.succ)))

lemma pairSlot_degree {p : ℕ} (u v : MvPolynomial (Fin (p + 1)) R)
    (F : MvPolynomial (Fin (p + 2)) R) (hu : u.totalDegree ≤ 1) (hv : v.totalDegree ≤ 1) :
    (pairSlot u v F).totalDegree ≤ F.totalDegree := by
  apply linear_mv_substitution_degree
  intro i
  refine Fin.cases hu (fun j => ?_) i
  exact Fin.cases hv (fun k => variable_degree_le_one _) j

lemma pairSlot_eval {p : ℕ} (u v : MvPolynomial (Fin (p + 1)) R)
    (F : MvPolynomial (Fin (p + 2)) R) (x : Fin (p + 1) → R) :
    MvPolynomial.eval x (pairSlot u v F) =
      MvPolynomial.eval (Fin.cases (MvPolynomial.eval x u)
        (Fin.cases (MvPolynomial.eval x v) (fun j => x j.succ))) F := by
  rw [pairSlot, substitution_eval]
  apply congrArg (fun z : Fin (p + 2) → R => MvPolynomial.eval z F)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · exact MvPolynomial.eval_X _

def jointHeadShift {p : ℕ} (c : R) (F : MvPolynomial (Fin (p + 1)) R) :
    MvPolynomial (Fin (p + 1)) R :=
  F.eval₂ MvPolynomial.C
    (Fin.cases (MvPolynomial.X 0 + MvPolynomial.C c) (fun j => MvPolynomial.X j.succ))

lemma jointHeadShift_degree {p : ℕ} (c : R) (F : MvPolynomial (Fin (p + 1)) R) :
    (jointHeadShift c F).totalDegree ≤ F.totalDegree := by
  apply linear_mv_substitution_degree
  intro i
  refine Fin.cases ?_ (fun j => variable_degree_le_one _) i
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le (variable_degree_le_one _) (by rw [MvPolynomial.totalDegree_C]; omega))

lemma jointHeadShift_eval {p : ℕ} (c n : R) (F : MvPolynomial (Fin (p + 1)) R)
    (tail : Fin p → R) :
    MvPolynomial.eval (Fin.cases n tail) (jointHeadShift c F) =
      MvPolynomial.eval (Fin.cases (n + c) tail) F := by
  rw [jointHeadShift, substitution_eval]
  apply congrArg (fun z : Fin (p + 1) → R => MvPolynomial.eval z F)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

def jointPairEventualPolynomial {p : ℕ} (b : ℕ) (F : MvPolynomial (Fin (p + 2)) R)
    (L Q : ℕ → MvPolynomial (Fin (p + 1)) R) : MvPolynomial (Fin (p + 1)) R :=
  jointDiagonalPolynomial F +
    (∑ a ∈ Finset.range (b + 1), jointHeadShift (-(a : R))
      (L a - pairSlot (MvPolynomial.C (a : R)) (MvPolynomial.X 0) F)) +
    ∑ a ∈ Finset.range (b + 1), jointHeadShift (-(a : R))
      (Q a - pairSlot (MvPolynomial.X 0) (MvPolynomial.C (a : R)) F)

lemma jointPairEventualPolynomial_degree {p : ℕ} (b D : ℕ)
    (F : MvPolynomial (Fin (p + 2)) R) (L Q : ℕ → MvPolynomial (Fin (p + 1)) R)
    (hF : F.totalDegree ≤ D) (hL : ∀ a ≤ b, (L a).totalDegree ≤ D)
    (hQ : ∀ a ≤ b, (Q a).totalDegree ≤ D) :
    (jointPairEventualPolynomial b F L Q).totalDegree ≤ D + 1 := by
  have hleft : (∑ a ∈ Finset.range (b + 1), jointHeadShift (-(a : R))
      (L a - pairSlot (MvPolynomial.C (a : R)) (MvPolynomial.X 0) F)).totalDegree ≤ D := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro a ha
    apply (jointHeadShift_degree _ _).trans
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le (hL a (by have := Finset.mem_range.mp ha; omega))
    exact (pairSlot_degree _ _ _ (by rw [MvPolynomial.totalDegree_C]; omega)
      (variable_degree_le_one _)).trans hF
  have hright : (∑ a ∈ Finset.range (b + 1), jointHeadShift (-(a : R))
      (Q a - pairSlot (MvPolynomial.X 0) (MvPolynomial.C (a : R)) F)).totalDegree ≤ D := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro a ha
    apply (jointHeadShift_degree _ _).trans
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le (hQ a (by have := Finset.mem_range.mp ha; omega))
    exact (pairSlot_degree _ _ _ (variable_degree_le_one _)
      (by rw [MvPolynomial.totalDegree_C]; omega)).trans hF
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le _ (hright.trans (by omega))
  apply (MvPolynomial.totalDegree_add _ _).trans
  exact max_le ((jointDiagonalPolynomial_degree F).trans (Nat.add_le_add_right hF 1))
    (hleft.trans (by omega))

lemma jointPairEventualPolynomial_eval {p : ℕ} (b n : ℕ)
    (F : MvPolynomial (Fin (p + 2)) R) (L Q : ℕ → MvPolynomial (Fin (p + 1)) R)
    (tail : Fin p → R) (f : ℕ → ℕ → R) (hn : 2 * b < n)
    (hinterior : ∀ u v : ℕ, u + v = n → b < u → b < v →
      f u v = MvPolynomial.eval (Fin.cases (u : R) (Fin.cases (v : R) tail)) F)
    (hleft : ∀ a ≤ b, f a (n - a) = MvPolynomial.eval (Fin.cases ((n - a : ℕ) : R) tail) (L a))
    (hright : ∀ a ≤ b, f (n - a) a = MvPolynomial.eval (Fin.cases ((n - a : ℕ) : R) tail) (Q a)) :
    MvPolynomial.eval (Fin.cases (n : R) tail) (jointPairEventualPolynomial b F L Q) =
      ∑ u ∈ Finset.range (n + 1), f u (n - u) := by
  let c : ℕ → ℕ → R := fun u v => f u v -
    MvPolynomial.eval (Fin.cases (u : R) (Fin.cases (v : R) tail)) F
  have hsplit := BoundaryPolynomial.pair_boundary_split c b n hn (by
    intro u v huv hu hv
    dsimp [c]
    rw [hinterior u v huv hu hv, sub_self])
  have hdiag : MvPolynomial.eval (Fin.cases (n : R) tail) (jointDiagonalPolynomial F) =
      ∑ u ∈ Finset.range (n + 1), MvPolynomial.eval
        (Fin.cases (u : R) (Fin.cases ((n - u : ℕ) : R) tail)) F := by
    rw [jointDiagonalPolynomial_eval]
    apply Finset.sum_congr rfl
    intro u hu
    have hu' : u ≤ n := by have := Finset.mem_range.mp hu; omega
    rw [Nat.cast_sub hu']
  have hl : MvPolynomial.eval (Fin.cases (n : R) tail)
      (∑ a ∈ Finset.range (b + 1), jointHeadShift (-(a : R))
        (L a - pairSlot (MvPolynomial.C (a : R)) (MvPolynomial.X 0) F)) =
      ∑ a ∈ Finset.range (b + 1), c a (n - a) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≤ b := by have := Finset.mem_range.mp ha; omega
    have han : a ≤ n := by omega
    rw [jointHeadShift_eval, map_sub, pairSlot_eval]
    simp only [MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.cases_zero, Fin.cases_succ]
    rw [← sub_eq_add_neg, ← Nat.cast_sub han, ← hleft a ha']
  have hq : MvPolynomial.eval (Fin.cases (n : R) tail)
      (∑ a ∈ Finset.range (b + 1), jointHeadShift (-(a : R))
        (Q a - pairSlot (MvPolynomial.X 0) (MvPolynomial.C (a : R)) F)) =
      ∑ a ∈ Finset.range (b + 1), c (n - a) a := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≤ b := by have := Finset.mem_range.mp ha; omega
    have han : a ≤ n := by omega
    rw [jointHeadShift_eval, map_sub, pairSlot_eval]
    simp only [MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.cases_zero, Fin.cases_succ]
    rw [← sub_eq_add_neg, ← Nat.cast_sub han, ← hright a ha']
  rw [jointPairEventualPolynomial, map_add, map_add, hdiag, hl, hq,
    add_assoc, ← hsplit, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  dsimp [c]
  ring
end WP.HigherOrder.JointBoundary
