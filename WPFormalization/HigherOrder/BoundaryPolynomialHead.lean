import WPFormalization.HigherOrder.Triangular
import WPFormalization.Analysis.PolynomialMomentReduction
import Mathlib
/-! Exact head and merger reductions from an actual boundary-polynomial stage certificate. The head and merger use uniform low-index cutoffs b+1 and b+2, before the physical parameter or the varying large degrees. The stage certificate remains an explicit inductive input: this module does not assert the all-order boundary-stratification theorem or complete C.3 finite-data dependence. -/
noncomputable section
namespace WP.HigherOrder.BoundaryPolynomial
open Set

lemma eval₂_linear_natDegree_le {ι : Type*} (P : MvPolynomial ι ℝ)
    (x : ι → Polynomial ℝ) (hx : ∀ i, (x i).natDegree ≤ 1) :
    (P.eval₂ Polynomial.C x).natDegree ≤ P.totalDegree := by
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply (Polynomial.natDegree_mul_le).trans
  rw [Polynomial.natDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ m.support, (x i ^ m i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Polynomial.natDegree_pow_le).trans (by nlinarith [hx i])
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hm

def classify (p b : ℕ) (d : Fin p → ℕ) : Fin p → Option (Fin (b + 1)) := fun i =>
  if hi : d i ≤ b then some ⟨d i, by omega⟩ else none

def headSubstitution {p : ℕ} (d : Fin p → ℕ) : Fin (p + 1) → Polynomial ℝ :=
  Fin.cases Polynomial.X (fun i => Polynomial.C (d i : ℝ))

def headPolynomial {p : ℕ} (P : MvPolynomial (Fin (p + 1)) ℝ) (d : Fin p → ℕ) : Polynomial ℝ :=
  P.eval₂ Polynomial.C (headSubstitution d)

lemma headPolynomial_degree {p : ℕ} (P : MvPolynomial (Fin (p + 1)) ℝ) (d : Fin p → ℕ) :
    (headPolynomial P d).natDegree ≤ P.totalDegree := by
  apply eval₂_linear_natDegree_le
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [headSubstitution]
  · simp [headSubstitution]

lemma headPolynomial_eval {p : ℕ} (P : MvPolynomial (Fin (p + 1)) ℝ) (d : Fin p → ℕ) (n : ℝ) :
    (headPolynomial P d).eval n = MvPolynomial.eval (Fin.cases n (fun i => (d i : ℝ))) P := by
  have he := MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom n) Polynomial.C (headSubstitution d) P
  have hC : (Polynomial.evalRingHom n).comp Polynomial.C = RingHom.id ℝ := by ext x; simp
  have hx : (fun i => Polynomial.eval n (headSubstitution d i)) =
      Fin.cases n (fun i => (d i : ℝ)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [headSubstitution]
  change Polynomial.eval n (P.eval₂ Polynomial.C (headSubstitution d)) =
    MvPolynomial.eval₂ (RingHom.id ℝ) (Fin.cases n (fun i => (d i : ℝ))) P
  simpa only [Polynomial.coe_evalRingHom, hC, Function.comp_def, hx] using he

lemma classify_large_head {p : ℕ} (b n : ℕ) (d : Fin p → ℕ) (hn : b < n) :
    classify (p + 1) b (Fin.cases n d) = Fin.cases none (classify p b d) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [classify, not_le.mpr hn]
  · change (if h : d j ≤ b then some (⟨d j, by omega⟩ : Fin (b + 1)) else none) =
      (if h : d j ≤ b then some (⟨d j, by omega⟩ : Fin (b + 1)) else none)
    rfl

lemma actual_profile_head_eventual_polynomial (P : PsiTheory) (p K b D : ℕ)
    (F : ℝ → (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) ℝ)
    (hdegree : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ σ, (F Y σ).totalDegree ≤ D)
    (hactual : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (p + 1) → ℕ,
      profileCoefficient P Y (List.ofFn d) K =
        MvPolynomial.eval (fun i => (d i : ℝ)) (F Y (classify (p + 1) b d)))
    (tail : Fin p → ℕ) :
    ∃ Q : ℝ → Polynomial ℝ,
      (∀ Y ∈ Icc (0 : ℝ) y₀, (Q Y).natDegree ≤ D) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ n : ℕ, b < n →
        profileCoefficient P Y (n :: List.ofFn tail) K = (Q Y).eval (n : ℝ) := by
  let σ : Fin (p + 1) → Option (Fin (b + 1)) := Fin.cases none (classify p b tail)
  let Q : ℝ → Polynomial ℝ := fun Y => headPolynomial (F Y σ) tail
  refine ⟨Q, fun Y hY => (headPolynomial_degree _ _).trans (hdegree Y hY σ), ?_⟩
  intro Y hY n hn
  have ha := hactual Y hY (Fin.cases n tail)
  rw [classify_large_head b n tail hn] at ha
  have hv : (fun i : Fin (p + 1) => ((Fin.cases n tail i : ℕ) : ℝ)) =
      Fin.cases (n : ℝ) (fun i => (tail i : ℝ)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  simpa only [Q, σ, headPolynomial_eval, List.ofFn_succ, Fin.cases_zero, Fin.cases_succ, hv] using ha
end WP.HigherOrder.BoundaryPolynomial
namespace WP.HigherOrder.BoundaryPolynomial
open Set
lemma actual_profile_head_dilaton_finite_sum (P : PsiTheory) (p K b D : ℕ)
    (F : ℝ → (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) ℝ)
    (hdegree : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ σ, (F Y σ).totalDegree ≤ D)
    (hactual : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (p + 1) → ℕ,
      profileCoefficient P Y (List.ofFn d) K =
        MvPolynomial.eval (fun i => (d i : ℝ)) (F Y (classify (p + 1) b d)))
    (tail : Fin p → ℕ) :
    ∃ Q : ℝ → Polynomial ℝ,
      (∀ Y ∈ Icc (0 : ℝ) y₀, (Q Y).natDegree ≤ D) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀,
        HasSum (fun n : ℕ => canonicalDilatonCoefficient Y n * profileCoefficient P Y (n :: List.ofFn tail) K)
          ((∑ k ∈ Finset.range (D + 1), (Q Y).coeff k * bMoment k Y) +
            ∑ n ∈ Finset.range (b + 1), canonicalDilatonCoefficient Y n *
              (profileCoefficient P Y (n :: List.ofFn tail) K - (Q Y).eval (n : ℝ))) := by
  obtain ⟨Q, hQ, htail⟩ := actual_profile_head_eventual_polynomial P p K b D F hdegree hactual tail
  refine ⟨Q, hQ, ?_⟩
  intro Y hY
  exact WP.Analysis.dilaton_polynomial_tail_hasSum Y (Q Y) D (b + 1) (hQ Y hY) _
    (fun n hn => htail Y hY n (by omega))
end WP.HigherOrder.BoundaryPolynomial
namespace WP.HigherOrder.BoundaryPolynomial
open Set
lemma actual_merger_head_kernel_finite_sum (P : PsiTheory) (p K b D : ℕ)
    (F : ℝ → (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) ℝ)
    (hdegree : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ σ, (F Y σ).totalDegree ≤ D)
    (hactual : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (p + 1) → ℕ,
      profileCoefficient P Y (List.ofFn d) K =
        MvPolynomial.eval (fun i => (d i : ℝ)) (F Y (classify (p + 1) b d)))
    (tail : Fin p → ℕ) (t a : ℕ) :
    ∃ Q : ℝ → Polynomial ℝ,
      (∀ Y ∈ Icc (0 : ℝ) y₀, (Q Y).natDegree ≤ D) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀,
        HasSum (fun l : ℕ => weight Y l *
          (if 1 ≤ t + a + l then profileCoefficient P Y ((t + a + l - 1) :: List.ofFn tail) K else 0))
          ((∑ k ∈ Finset.range (D + 1), (Q Y).coeff k * kernelMoment k Y) +
            ∑ l ∈ Finset.range (b + 2), weight Y l *
              ((if 1 ≤ t + a + l then profileCoefficient P Y ((t + a + l - 1) :: List.ofFn tail) K else 0) -
                (Q Y).eval (l : ℝ))) := by
  obtain ⟨H, hH, htail⟩ := actual_profile_head_eventual_polynomial P p K b D F hdegree hactual tail
  let shift : Polynomial ℝ := Polynomial.X + Polynomial.C ((t : ℝ) + a - 1)
  let Q : ℝ → Polynomial ℝ := fun Y => (H Y).comp shift
  have hs : shift.natDegree ≤ 1 := by
    dsimp only [shift]
    apply (Polynomial.natDegree_add_le (Polynomial.X : Polynomial ℝ) (Polynomial.C ((t : ℝ) + (a : ℝ) - 1))).trans
    exact max_le Polynomial.natDegree_X_le (by rw [Polynomial.natDegree_C]; omega)
  have hQ (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) : (Q Y).natDegree ≤ D := by
    apply Polynomial.natDegree_comp_le.trans
    exact (Nat.mul_le_mul (hH Y hY) hs).trans_eq (Nat.mul_one _)
  refine ⟨Q, hQ, ?_⟩
  intro Y hY
  apply WP.Analysis.kernel_polynomial_tail_hasSum Y hY (Q Y) D (b + 2) (hQ Y hY)
  intro l hl
  have hvalid : 1 ≤ t + a + l := by omega
  rw [ite_eq_left hvalid, htail Y hY _ (by omega)]
  change (H Y).eval ((t + a + l - 1 : ℕ) : ℝ) = ((H Y).comp shift).eval (l : ℝ)
  rw [Polynomial.eval_comp]
  congr 1
  simp only [shift, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Nat.cast_sub hvalid, Nat.cast_add, Nat.cast_one]
  ring
end WP.HigherOrder.BoundaryPolynomial
