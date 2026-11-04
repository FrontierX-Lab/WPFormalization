import WPFormalization.HigherOrder.BoundaryAffineMoment
import WPFormalization.HigherOrder.MultivariatePowerSums
/-! The full two-head diagonal sum is a joint polynomial in its total and all remaining degrees. Its explicit substitution and multivariate Faulhaber construction increase total degree by at most one. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma substitution_eval {ι κ : Type*} (F : MvPolynomial ι R)
    (s : ι → MvPolynomial κ R) (x : κ → R) :
    MvPolynomial.eval x (F.eval₂ MvPolynomial.C s) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (s i)) F := by
  have he := MvPolynomial.eval₂_comp_left (MvPolynomial.eval x) MvPolynomial.C s F
  have hc : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id R := by ext a; simp
  change MvPolynomial.eval x (F.eval₂ MvPolynomial.C s) =
    MvPolynomial.eval₂ (RingHom.id R) _ F
  simpa only [hc, Function.comp_def] using he

def diagonalIntegrandAssignment (p : ℕ) : Fin (p + 2) → MvPolynomial (Fin (p + 2)) R :=
  Fin.cases (MvPolynomial.X 0)
    (Fin.cases (MvPolynomial.X 1 - MvPolynomial.X 0) (fun i => MvPolynomial.X i.succ.succ))

def diagonalCollapseAssignment (p : ℕ) : Fin (p + 2) → MvPolynomial (Fin (p + 1)) R :=
  Fin.cases (MvPolynomial.X 0 + 1)
    (Fin.cases (MvPolynomial.X 0) (fun i => MvPolynomial.X i.succ))

def jointDiagonalPolynomial {p : ℕ} (F : MvPolynomial (Fin (p + 2)) R) :
    MvPolynomial (Fin (p + 1)) R :=
  (BoundaryPolynomial.firstVariableSumPolynomial
    (F.eval₂ MvPolynomial.C (diagonalIntegrandAssignment p))).eval₂ MvPolynomial.C
      (diagonalCollapseAssignment p)

lemma jointDiagonalPolynomial_degree {p : ℕ} (F : MvPolynomial (Fin (p + 2)) R) :
    (jointDiagonalPolynomial F).totalDegree ≤ F.totalDegree + 1 := by
  have hi : ∀ i : Fin (p + 2), (diagonalIntegrandAssignment p i : MvPolynomial (Fin (p + 2)) R).totalDegree ≤ 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact variable_degree_le_one _
    · refine Fin.cases ?_ (fun k => ?_) j
      · exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (variable_degree_le_one _) (variable_degree_le_one _))
      · exact variable_degree_le_one _
  have hc : ∀ i : Fin (p + 2), (diagonalCollapseAssignment p i : MvPolynomial (Fin (p + 1)) R).totalDegree ≤ 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (MvPolynomial.totalDegree_add _ _).trans (max_le (variable_degree_le_one _) (by simp))
    · refine Fin.cases ?_ (fun k => ?_) j <;> exact variable_degree_le_one _
  exact (linear_mv_substitution_degree _ _ hc).trans
    ((BoundaryPolynomial.firstVariableSumPolynomial_degree _).trans
      (Nat.add_le_add_right (linear_mv_substitution_degree F _ hi) 1))

lemma jointDiagonalPolynomial_eval {p : ℕ} (F : MvPolynomial (Fin (p + 2)) R)
    (n : ℕ) (tail : Fin p → R) :
    MvPolynomial.eval (Fin.cases (n : R) tail) (jointDiagonalPolynomial F) =
      ∑ u ∈ Finset.range (n + 1), MvPolynomial.eval
        (Fin.cases (u : R) (Fin.cases ((n : R) - (u : R)) tail)) F := by
  have hc : (fun i => MvPolynomial.eval (Fin.cases (n : R) tail)
      (diagonalCollapseAssignment p i : MvPolynomial (Fin (p + 1)) R)) =
      Fin.cases ((n + 1 : ℕ) : R) (Fin.cases (n : R) tail) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [diagonalCollapseAssignment]
    · refine Fin.cases ?_ (fun k => ?_) j
      · change MvPolynomial.eval (Fin.cases (n : R) tail) (MvPolynomial.X (0 : Fin (p + 1))) = (n : R)
        simp
      · change MvPolynomial.eval (Fin.cases (n : R) tail) (MvPolynomial.X k.succ) = tail k
        simp
  rw [jointDiagonalPolynomial, substitution_eval, hc,
    BoundaryPolynomial.firstVariableSumPolynomial_eval]
  apply Finset.sum_congr rfl
  intro u hu
  rw [substitution_eval]
  apply congrArg (fun z : Fin (p + 2) → R => MvPolynomial.eval z F)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [diagonalIntegrandAssignment]
  · refine Fin.cases ?_ (fun k => ?_) j
    · change MvPolynomial.eval (Fin.cases (u : R) (Fin.cases (n : R) tail))
        (MvPolynomial.X (1 : Fin (p + 2)) - MvPolynomial.X 0) = (n : R) - (u : R)
      simp only [map_sub, MvPolynomial.eval_X, Fin.cases_zero]
      congr 1
    · change MvPolynomial.eval (Fin.cases (u : R) (Fin.cases (n : R) tail))
        (MvPolynomial.X k.succ.succ) = tail k
      simp
end WP.HigherOrder.JointBoundary
