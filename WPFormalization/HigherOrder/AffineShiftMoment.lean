import WPFormalization.HigherOrder.BoundaryAffineMoment
import WPFormalization.HigherOrder.ShiftExtraction
/-! Every integer complexity shift has exact finite integer coefficient weights, including order zero. Combining them with the actual affine moment recipe gives the genuine shifted canonical merger head as a joint finite-data polynomial. No convergence of the inverse-complexity formal series is assumed. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
open PowerSeries

def integerShiftWeight (c : ℤ) (n i : ℕ) : ℤ :=
  if n = 0 then if i = 0 then 1 else 0
  else if 1 ≤ i then (Nat.choose (n - 1) (i - 1) : ℤ) * c ^ (n - i) else 0

lemma complexityShift_coeff_integer_weights (c : ℤ) (f : Series) (n : ℕ) :
    PowerSeries.coeff n (complexityShift (c : ℝ) f) =
      ∑ i ∈ Finset.range (n + 1), (integerShiftWeight c n i : ℝ) * PowerSeries.coeff i f := by
  by_cases hn : n = 0
  · subst n
    simp [integerShiftWeight, PowerSeries.coeff_zero_eq_constantCoeff]
  · rw [complexityShift_coeff_sum_positive (c : ℝ) f n (by omega)]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hi' : 1 ≤ i
    · simp only [integerShiftWeight, ite_eq_right hn, ite_eq_left hi', Int.cast_mul,
        Int.cast_natCast, Int.cast_pow]
      ring
    · simp only [integerShiftWeight, ite_eq_right hn, ite_eq_right hi', Int.cast_zero, zero_mul]

variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma eval₂_integer {ι : Type*} (φ : R →+* ℝ) (x : ι → ℝ) (z : ℤ) :
    MvPolynomial.eval₂ φ x (z : MvPolynomial ι R) = (z : ℝ) := by
  change (MvPolynomial.eval₂Hom φ x) (z : MvPolynomial ι R) = (z : ℝ)
  exact map_intCast _ _

def affineShiftMomentPolynomial {p q : ℕ} (b c B n : ℕ) (s : ℤ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : ℕ → (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (M W : ℕ → R) : MvPolynomial (Fin p) R :=
  ∑ i ∈ Finset.range (n + 1), MvPolynomial.C (integerShiftWeight s n i : R) *
    affineMomentPolynomial b c B a σ e (F i) M W

lemma affineShiftMomentPolynomial_degree {p q : ℕ} (b c B n D : ℕ) (s : ℤ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : ℕ → (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ i ≤ n, ∀ τ, (F i τ).totalDegree ≤ D) (M W : ℕ → R) :
    (affineShiftMomentPolynomial b c B n s a σ e F M W).totalDegree ≤ D := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact affineMomentPolynomial_degree b c B D a σ e (F i)
    (hdegree i (by have := Finset.mem_range.mp hi; omega)) M W

lemma actual_affine_shifted_kernel_recipe (P : PsiTheory) (p q n b c B D : ℕ)
    (hB : b + c ≤ B) (s : ℤ) (a : Fin p → ℕ) (e : Fin q → Fin p)
    (F : ℕ → (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ i ≤ n, ∀ τ, (F i τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ i ≤ n, ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ v : Fin (q + 1) → ℕ,
      profileCoefficient P Y (List.ofFn v) i =
        MvPolynomial.eval₂ (φ Y) (fun j => (v j : ℝ)) (F i (classify (q + 1) b v)))
    (M W : ℕ → R) (w : ℝ → ℕ → ℝ)
    (hm : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * w Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ l : ℕ, l < b + c + 1 → w Y l = (φ Y) (W l)) :
    ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ,
      HasSum (fun l : ℕ => w Y l *
        (if c ≤ (∑ j : Fin p, a j * d j) + l then
          PowerSeries.coeff n (complexityShift (s : ℝ) (formalProfile P Y
            (((∑ j : Fin p, a j * d j) + l - c) :: List.ofFn (fun j => d (e j))))) else 0))
        (MvPolynomial.eval₂ (φ Y) (fun j => (d j : ℝ))
          (affineShiftMomentPolynomial b c B n s a (classify p B d) e F M W)) := by
  intro Y hY d
  have hh (i : ℕ) (hi : i ≤ n) :=
    actual_profile_affine_moment_recipe P p q i b c B D hB a e (F i)
      (hdegree i hi) φ (hactual i hi) M W w hm hw Y hY d
  have hsum := hasSum_sum (s := Finset.range (n + 1)) (fun i hi =>
    (hh i (by have := Finset.mem_range.mp hi; omega)).mul_left (integerShiftWeight s n i : ℝ))
  convert! hsum using 1
  · funext l
    by_cases hl : c ≤ (∑ j : Fin p, a j * d j) + l
    · simp only [ite_eq_left hl, complexityShift_coeff_integer_weights, Finset.mul_sum,
        formalProfile, PowerSeries.coeff_mk]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · simp only [ite_eq_right hl, mul_zero, Finset.sum_const_zero]
  · simp only [affineShiftMomentPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, map_intCast, eval₂_integer]
end WP.HigherOrder.JointBoundary
