import WPFormalization.HigherOrder.JointDiagonalStrata
import WPFormalization.HigherOrder.AffineShiftMoment
/-! Exact coefficient recipes for the actual canonical merger and nonseparating coefficientSum kernels, including the genuine integer complexity shifts. HasSum is proved from finite moments and corrections, and the nonseparating range t+l-1 matches its invalid-degree branch. Current lower profile-stratum certificates remain explicit inductive inputs. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
open PowerSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def affinePairShiftMomentPolynomial {p q : ℕ} (b B n : ℕ) (s : ℤ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : ℕ → (Fin (q + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 2)) R)
    (M W : ℕ → R) : MvPolynomial (Fin p) R :=
  ∑ i ∈ Finset.range (n + 1), MvPolynomial.C (integerShiftWeight s n i : R) *
    affinePairMomentPolynomial b B a σ e (F i) M W

lemma affinePairShiftMomentPolynomial_degree {p q : ℕ} (b B n D : ℕ) (s : ℤ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : ℕ → (Fin (q + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 2)) R)
    (hdegree : ∀ i ≤ n, ∀ τ, (F i τ).totalDegree ≤ D) (M W : ℕ → R) :
    (affinePairShiftMomentPolynomial b B n s a σ e F M W).totalDegree ≤ D + 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact affinePairMomentPolynomial_degree b B D a σ e (F i)
    (hdegree i (by have := Finset.mem_range.mp hi; omega)) M W

lemma actual_affine_pair_shifted_kernel_recipe (P : PsiTheory) (p q n b B D : ℕ)
    (hB : 2 * b + 2 ≤ B) (s : ℤ) (a : Fin p → ℕ) (e : Fin q → Fin p)
    (F : ℕ → (Fin (q + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 2)) R)
    (hdegree : ∀ i ≤ n, ∀ τ, (F i τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ i ≤ n, ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ v : Fin (q + 2) → ℕ,
      profileCoefficient P Y (List.ofFn v) i =
        MvPolynomial.eval₂ (φ Y) (fun j => (v j : ℝ)) (F i (classify (q + 2) b v)))
    (M W : ℕ → R) (w : ℝ → ℕ → ℝ)
    (hm : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D + 1 →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * w Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ l : ℕ, l < 2 * b + 3 → w Y l = (φ Y) (W l)) :
    ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ,
      HasSum (fun l : ℕ => w Y l *
        (if 2 ≤ (∑ j : Fin p, a j * d j) + l then
          ∑ u ∈ Finset.range ((∑ j : Fin p, a j * d j) + l - 2 + 1),
            PowerSeries.coeff n (complexityShift (s : ℝ) (formalProfile P Y
              (u :: ((∑ j : Fin p, a j * d j) + l - 2 - u) ::
                List.ofFn (fun j => d (e j))))) else 0))
        (MvPolynomial.eval₂ (φ Y) (fun j => (d j : ℝ))
          (affinePairShiftMomentPolynomial b B n s a (classify p B d) e F M W)) := by
  intro Y hY d
  have hh (i : ℕ) (hi : i ≤ n) :=
    actual_profile_affine_pair_moment_recipe P p q i b B D hB a e (F i)
      (hdegree i hi) φ (hactual i hi) M W w hm hw Y hY d
  have hsum := hasSum_sum (s := Finset.range (n + 1)) (fun i hi =>
    (hh i (by have := Finset.mem_range.mp hi; omega)).mul_left (integerShiftWeight s n i : ℝ))
  convert! hsum using 1
  · funext l
    by_cases hl : 2 ≤ (∑ j : Fin p, a j * d j) + l
    · simp only [ite_eq_left hl, complexityShift_coeff_integer_weights, Finset.mul_sum,
        formalProfile, PowerSeries.coeff_mk]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro u hu
      ring
    · simp only [ite_eq_right hl, mul_zero, Finset.sum_const_zero]
  · simp only [affinePairShiftMomentPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, map_intCast, eval₂_integer]


lemma actual_affine_merger_kernel_coefficient_recipe (P : PsiTheory) (p q n b c B D : ℕ)
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
      PowerSeries.coeff n (coefficientSum (fun l : ℕ =>
        if c ≤ (∑ j : Fin p, a j * d j) + l then
          C (w Y l) * complexityShift (s : ℝ) (formalProfile P Y
            (((∑ j : Fin p, a j * d j) + l - c) :: List.ofFn (fun j => d (e j)))) else 0)) =
        MvPolynomial.eval₂ (φ Y) (fun j => (d j : ℝ))
          (affineShiftMomentPolynomial b c B n s a (classify p B d) e F M W) := by
  intro Y hY d
  have hs := actual_affine_shifted_kernel_recipe P p q n b c B D hB s a e F
    hdegree φ hactual M W w hm hw Y hY d
  rw [coefficientSum_coeff]
  convert! hs.tsum_eq using 1
  congr 1
  funext l
  by_cases hl : c ≤ (∑ j : Fin p, a j * d j) + l
  · simp only [ite_eq_left hl, PowerSeries.coeff_C_mul]
  · simp only [ite_eq_right hl, map_zero, mul_zero]

lemma actual_affine_handle_kernel_coefficient_recipe (P : PsiTheory) (p q n b B D : ℕ)
    (hB : 2 * b + 2 ≤ B) (s : ℤ) (a : Fin p → ℕ) (e : Fin q → Fin p)
    (F : ℕ → (Fin (q + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 2)) R)
    (hdegree : ∀ i ≤ n, ∀ τ, (F i τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ i ≤ n, ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ v : Fin (q + 2) → ℕ,
      profileCoefficient P Y (List.ofFn v) i =
        MvPolynomial.eval₂ (φ Y) (fun j => (v j : ℝ)) (F i (classify (q + 2) b v)))
    (M W : ℕ → R) (w : ℝ → ℕ → ℝ)
    (hm : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D + 1 →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * w Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ l : ℕ, l < 2 * b + 3 → w Y l = (φ Y) (W l)) :
    ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ,
      PowerSeries.coeff n (coefficientSum (fun l : ℕ => C (w Y l) *
        ∑ u ∈ Finset.range ((∑ j : Fin p, a j * d j) + l - 1),
          complexityShift (s : ℝ) (formalProfile P Y
            (u :: ((∑ j : Fin p, a j * d j) + l - 2 - u) ::
              List.ofFn (fun j => d (e j)))))) =
        MvPolynomial.eval₂ (φ Y) (fun j => (d j : ℝ))
          (affinePairShiftMomentPolynomial b B n s a (classify p B d) e F M W) := by
  intro Y hY d
  have hs := actual_affine_pair_shifted_kernel_recipe P p q n b B D hB s a e F
    hdegree φ hactual M W w hm hw Y hY d
  rw [coefficientSum_coeff]
  convert! hs.tsum_eq using 1
  congr 1
  funext l
  by_cases hl : 2 ≤ (∑ j : Fin p, a j * d j) + l
  · have hlen : (∑ j : Fin p, a j * d j) + l - 1 =
        (∑ j : Fin p, a j * d j) + l - 2 + 1 := by omega
    simp only [ite_eq_left hl, hlen, PowerSeries.coeff_C_mul, map_sum]
  · have hlen : (∑ j : Fin p, a j * d j) + l - 1 = 0 := by omega
    simp only [ite_eq_right hl, hlen, Finset.range_zero, Finset.sum_empty,
      mul_zero, map_zero]
end WP.HigherOrder.JointBoundary
