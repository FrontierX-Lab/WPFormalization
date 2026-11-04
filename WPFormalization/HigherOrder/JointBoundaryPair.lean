import WPFormalization.HigherOrder.PairEventualPolynomial
/-! Joint finite-data recipes for the genuine nonseparating kernel head. A current actual profile-stratum certificate supplies one eventual diagonal polynomial, both finite boundary corrections, and an exact weighted HasSum using moments only through D+1 and low weights through 2b+2. The cutoff is uniform before the pivot, all tail degrees and Y. The all-order certificates themselves are not asserted here. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
open Set
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma linear_mv_substitution_degree {ι κ : Type*} (P : MvPolynomial ι R)
    (x : ι → MvPolynomial κ R) (hx : ∀ i, (x i).totalDegree ≤ 1) :
    (P.eval₂ MvPolynomial.C x).totalDegree ≤ P.totalDegree := by
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ m.support, (x i ^ m i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (MvPolynomial.totalDegree_pow _ _).trans (by nlinarith [hx i])
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hm

def pairSubstitution {p : ℕ} (tail : Fin p → ℕ) :
    Fin (p + 2) → MvPolynomial (Fin 2) R :=
  Fin.cases (MvPolynomial.X 0)
    (Fin.cases (MvPolynomial.X 1) (fun i => MvPolynomial.C (tail i : R)))

def pairSpecialization {p : ℕ} (F : MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) : MvPolynomial (Fin 2) R :=
  F.eval₂ MvPolynomial.C (pairSubstitution tail)

lemma pairSpecialization_degree {p : ℕ} (F : MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) : (pairSpecialization F tail).totalDegree ≤ F.totalDegree := by
  have hX (i : Fin 2) : (MvPolynomial.X i : MvPolynomial (Fin 2) R).totalDegree ≤ 1 := by
    change (MvPolynomial.monomial (Finsupp.single i 1) (1 : R)).totalDegree ≤ 1
    simpa using (MvPolynomial.totalDegree_monomial_le (Finsupp.single i 1) (1 : R))
  apply linear_mv_substitution_degree
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) R).totalDegree ≤ 1
    exact hX 0
  · refine Fin.cases ?_ (fun k => ?_) j
    · change (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) R).totalDegree ≤ 1
      exact hX 1
    · change (MvPolynomial.C (tail k : R) : MvPolynomial (Fin 2) R).totalDegree ≤ 1
      rw [MvPolynomial.totalDegree_C]
      omega

lemma pairSpecialization_eval {p : ℕ} (F : MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) (u v : R) :
    BoundaryPolynomial.pairValue (pairSpecialization F tail) u v =
      MvPolynomial.eval (Fin.cases u (Fin.cases v (fun i => (tail i : R)))) F := by
  have he := MvPolynomial.eval₂_comp_left
    (MvPolynomial.eval (Fin.cases u (fun _ : Fin 1 => v))) MvPolynomial.C
    (pairSubstitution tail) F
  have hc : (MvPolynomial.eval (Fin.cases u (fun _ : Fin 1 => v))).comp MvPolynomial.C =
      RingHom.id R := by ext x; simp
  have hx : (fun i => MvPolynomial.eval (Fin.cases u (fun _ : Fin 1 => v))
      (pairSubstitution tail i)) =
      Fin.cases u (Fin.cases v (fun i => (tail i : R))) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [pairSubstitution]
    · refine Fin.cases ?_ (fun k => ?_) j
      · change (MvPolynomial.eval (Fin.cases u (fun _ : Fin 1 => v))) (MvPolynomial.X (1 : Fin 2)) = v
        rw [MvPolynomial.eval_X]
        exact Fin.cases_succ (motive := fun _ : Fin 2 => R) (zero := u) (succ := fun _ : Fin 1 => v) 0
      · change (MvPolynomial.eval (Fin.cases u (fun _ : Fin 1 => v))) (MvPolynomial.C (tail k : R)) = (tail k : R)
        exact MvPolynomial.eval_C _
  change (MvPolynomial.eval (Fin.cases u (fun _ : Fin 1 => v)))
      (F.eval₂ MvPolynomial.C (pairSubstitution tail)) =
    MvPolynomial.eval₂ (RingHom.id R)
      (Fin.cases u (Fin.cases v (fun i => (tail i : R)))) F
  simpa only [hc, Function.comp_def, hx] using he

lemma classify_pair {p : ℕ} (b u v : ℕ) (tail : Fin p → ℕ) :
    classify (p + 2) b (Fin.cases u (Fin.cases v tail)) =
      Fin.cases (classify 1 b (fun _ => u) 0)
        (Fin.cases (classify 1 b (fun _ => v) 0) (classify p b tail)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j <;> rfl

lemma cast_pair {p : ℕ} (u v : ℕ) (tail : Fin p → ℕ) :
    (fun i : Fin (p + 2) => ((Fin.cases u (Fin.cases v tail) i : ℕ) : R)) =
      Fin.cases (u : R) (Fin.cases (v : R) (fun i => (tail i : R))) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j <;> rfl

def pairHighPolynomial {p : ℕ} (b : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) : MvPolynomial (Fin 2) R :=
  pairSpecialization (F (Fin.cases none (Fin.cases none (classify p b tail)))) tail

def pairLeftPolynomial {p : ℕ} (b : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) (a : ℕ) : Polynomial R :=
  BoundaryPolynomial.leftSection
    (pairSpecialization (F (Fin.cases (classify 1 b (fun _ => a) 0)
      (Fin.cases none (classify p b tail)))) tail) (a : R)

def pairRightPolynomial {p : ℕ} (b : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) (a : ℕ) : Polynomial R :=
  BoundaryPolynomial.rightSection
    (pairSpecialization (F (Fin.cases none
      (Fin.cases (classify 1 b (fun _ => a) 0) (classify p b tail)))) tail) (a : R)

def pairHeadPolynomial {p : ℕ} (b : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) : Polynomial R :=
  BoundaryPolynomial.pairEventualPolynomial b (pairHighPolynomial b F tail)
    (pairLeftPolynomial b F tail) (pairRightPolynomial b F tail)

lemma pairHeadPolynomial_degree {p : ℕ} (b D : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (hdegree : ∀ σ, (F σ).totalDegree ≤ D) (tail : Fin p → ℕ) :
    (pairHeadPolynomial b F tail).natDegree ≤ D + 1 := by
  apply BoundaryPolynomial.pairEventualPolynomial_degree
  · exact (pairSpecialization_degree _ _).trans (hdegree _)
  · intro a ha
    exact ((BoundaryPolynomial.leftSection_degree _ _).trans
      (pairSpecialization_degree _ _)).trans (hdegree _)
  · intro a ha
    exact ((BoundaryPolynomial.rightSection_degree _ _).trans
      (pairSpecialization_degree _ _)).trans (hdegree _)

lemma pairHeadPolynomial_eval {p : ℕ} (b n : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) (hn : 2 * b < n) :
    (pairHeadPolynomial b F tail).eval (n : R) =
      ∑ u ∈ Finset.range (n + 1),
        profileRecipeValue b F (Fin.cases u (Fin.cases (n - u) tail)) := by
  unfold pairHeadPolynomial
  apply BoundaryPolynomial.pairEventualPolynomial_eval b n (pairHighPolynomial b F tail)
    (pairLeftPolynomial b F tail) (pairRightPolynomial b F tail)
    (fun u v => profileRecipeValue b F (Fin.cases u (Fin.cases v tail))) hn
  · intro u v huv hu hv
    rw [pairHighPolynomial, pairSpecialization_eval]
    unfold profileRecipeValue
    rw [classify_pair]
    simp only [classify, not_le.mpr hu, not_le.mpr hv, dite_false, cast_pair]
  · intro a ha
    rw [pairLeftPolynomial, BoundaryPolynomial.leftSection_eval, pairSpecialization_eval]
    unfold profileRecipeValue
    rw [classify_pair]
    have hv : b < n - a := by omega
    simp only [classify, not_le.mpr hv, dite_false, cast_pair]
  · intro a ha
    rw [pairRightPolynomial, BoundaryPolynomial.rightSection_eval, pairSpecialization_eval]
    unfold profileRecipeValue
    rw [classify_pair]
    have hu : b < n - a := by omega
    simp only [classify, not_le.mpr hu, dite_false, cast_pair]


def pairKernelValue {p : ℕ} (b : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) (t l : ℕ) : R :=
  if 2 ≤ t + l then
    ∑ u ∈ Finset.range (t + l - 2 + 1),
      profileRecipeValue b F (Fin.cases u (Fin.cases (t + l - 2 - u) tail))
  else 0

def pairKernelPolynomial {p : ℕ} (b : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) (t : ℕ) : Polynomial R :=
  (pairHeadPolynomial b F tail).comp (Polynomial.X + Polynomial.C ((t : R) - 2))

lemma pairKernelPolynomial_degree {p : ℕ} (b D : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (hdegree : ∀ σ, (F σ).totalDegree ≤ D) (tail : Fin p → ℕ) (t : ℕ) :
    (pairKernelPolynomial b F tail t).natDegree ≤ D + 1 := by
  apply Polynomial.natDegree_comp_le.trans
  apply (Nat.mul_le_mul (pairHeadPolynomial_degree b D F hdegree tail)
    ((Polynomial.natDegree_add_le _ _).trans
      (max_le Polynomial.natDegree_X_le (by simp)))).trans_eq
  exact Nat.mul_one _

lemma pairKernelPolynomial_eval {p : ℕ} (b : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) (t l : ℕ) (hl : 2 * b + 3 ≤ l) :
    (pairKernelPolynomial b F tail t).eval (l : R) = pairKernelValue b F tail t l := by
  have hv : 2 ≤ t + l := by omega
  have hn : 2 * b < t + l - 2 := by omega
  rw [pairKernelPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  have hc : (l : R) + ((t : R) - 2) = ((t + l - 2 : ℕ) : R) := by
    rw [Nat.cast_sub hv, Nat.cast_add]
    push_cast
    ring
  rw [hc, pairHeadPolynomial_eval b (t + l - 2) F tail hn, pairKernelValue, if_pos hv]

def pairKernelMomentRecipe {p : ℕ} (b D : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (tail : Fin p → ℕ) (t : ℕ) (M W : ℕ → R) : R :=
  BoundaryPolynomial.polynomialMomentRecipe (pairKernelPolynomial b F tail t)
    M W (pairKernelValue b F tail t) (D + 1) (2 * b + 3)

lemma actual_profile_pair_moment_recipe (P : PsiTheory) (p K b D : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (hdegree : ∀ σ, (F σ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (p + 2) → ℕ,
      profileCoefficient P Y (List.ofFn d) K =
        MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (F (classify (p + 2) b d)))
    (tail : Fin p → ℕ) (t : ℕ) (M W : ℕ → R) (w : ℝ → ℕ → ℝ)
    (hm : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D + 1 →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * w Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ l : ℕ, l < 2 * b + 3 → w Y l = (φ Y) (W l)) :
    ∀ Y ∈ Icc (0 : ℝ) y₀,
      HasSum (fun l : ℕ => w Y l *
        (if 2 ≤ t + l then ∑ u ∈ Finset.range (t + l - 2 + 1),
          profileCoefficient P Y (u :: (t + l - 2 - u) :: List.ofFn tail) K else 0))
        ((φ Y) (pairKernelMomentRecipe b D F tail t M W)) := by
  intro Y hY
  have hval : ∀ l : ℕ,
      (if 2 ≤ t + l then ∑ u ∈ Finset.range (t + l - 2 + 1),
          profileCoefficient P Y (u :: (t + l - 2 - u) :: List.ofFn tail) K else 0) =
        (φ Y) (pairKernelValue b F tail t l) := by
    intro l
    by_cases hl : 2 ≤ t + l
    · simp only [pairKernelValue, if_pos hl, map_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [profileRecipeValue_eval]
      have he := hactual Y hY (Fin.cases u (Fin.cases (t + l - 2 - u) tail))
      simpa only [List.ofFn_succ, Fin.cases_zero, Fin.cases_succ] using he
    · simp only [pairKernelValue, if_neg hl, map_zero]
  apply BoundaryPolynomial.polynomialMomentRecipe_hasSum (φ Y)
    (pairKernelPolynomial b F tail t) M W (pairKernelValue b F tail t)
    (D + 1) (2 * b + 3) (pairKernelPolynomial_degree b D F hdegree tail t)
    (w Y) _ (hm Y hY) (hw Y hY)
  · intro l hl
    exact hval l
  · intro l hl
    rw [hval l, BoundaryPolynomial.map_polynomial_eval_nat, pairKernelPolynomial_eval b F tail t l hl]
end WP.HigherOrder.JointBoundary
