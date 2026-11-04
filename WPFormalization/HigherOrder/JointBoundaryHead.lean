import WPFormalization.HigherOrder.FinitePolynomialMomentAlgebra
import WPFormalization.HigherOrder.Triangular
/-! Joint finite-data and degree-variable head recipes. A current actual profile-stratum certificate over any coefficient ring yields an explicit finite algebraic moment recipe, uniform before the real parameter. Taking that ring to be multivariate polynomials in actual finite data retains literal polynomial dependence; no prefix-agreement or all-order certificate is assumed as an external theorem. The current certificate remains an explicit inductive input. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
open Set
variable {R : Type*} [CommRing R]

lemma linear_substitution_degree {ι : Type*} (P : MvPolynomial ι R)
    (x : ι → Polynomial R) (hx : ∀ i, (x i).natDegree ≤ 1) :
    (P.eval₂ Polynomial.C x).natDegree ≤ P.totalDegree := by
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply Polynomial.natDegree_mul_le.trans
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

lemma classify_large_head {p : ℕ} (b n : ℕ) (d : Fin p → ℕ) (hn : b < n) :
    classify (p + 1) b (Fin.cases n d) = Fin.cases none (classify p b d) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [classify, not_le.mpr hn]
  · change (if h : d j ≤ b then some (⟨d j, by omega⟩ : Fin (b + 1)) else none) =
      (if h : d j ≤ b then some (⟨d j, by omega⟩ : Fin (b + 1)) else none)
    rfl

def headSubstitution {p : ℕ} (d : Fin p → ℕ) : Fin (p + 1) → Polynomial R :=
  Fin.cases Polynomial.X (fun i => Polynomial.C (d i : R))

def headPolynomial {p : ℕ} (F : MvPolynomial (Fin (p + 1)) R) (d : Fin p → ℕ) : Polynomial R :=
  F.eval₂ Polynomial.C (headSubstitution d)

lemma headPolynomial_degree {p : ℕ} (F : MvPolynomial (Fin (p + 1)) R) (d : Fin p → ℕ) :
    (headPolynomial F d).natDegree ≤ F.totalDegree := by
  apply linear_substitution_degree
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Polynomial.natDegree_X_le
  · simp [headSubstitution]

lemma headPolynomial_eval₂ {p : ℕ} (F : MvPolynomial (Fin (p + 1)) R) (d : Fin p → ℕ)
    (φ : R →+* ℝ) (n : ℝ) :
    Polynomial.eval₂ φ n (headPolynomial F d) =
      MvPolynomial.eval₂ φ (Fin.cases n (fun i => (d i : ℝ))) F := by
  have he := MvPolynomial.eval₂_comp_left (Polynomial.eval₂RingHom φ n) Polynomial.C (headSubstitution d) F
  have hC : (Polynomial.eval₂RingHom φ n).comp Polynomial.C = φ := by ext x; simp
  have hx : (fun i => Polynomial.eval₂ φ n (headSubstitution d i)) =
      Fin.cases n (fun i => (d i : ℝ)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [headSubstitution]
  change Polynomial.eval₂ φ n (F.eval₂ Polynomial.C (headSubstitution d)) = _
  simpa only [Polynomial.coe_eval₂RingHom, hC, Function.comp_def, hx] using he

def profileRecipeValue {p : ℕ} (b : ℕ)
    (F : (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R)
    (d : Fin (p + 1) → ℕ) : R :=
  MvPolynomial.eval (fun i => (d i : R)) (F (classify (p + 1) b d))

lemma profileRecipeValue_eval {p : ℕ} (b : ℕ)
    (F : (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R)
    (d : Fin (p + 1) → ℕ) (φ : R →+* ℝ) :
    φ (profileRecipeValue b F d) =
      MvPolynomial.eval₂ φ (fun i => (d i : ℝ)) (F (classify (p + 1) b d)) := by
  have he := MvPolynomial.eval₂_comp_left φ (RingHom.id R) (fun i => (d i : R)) (F (classify (p + 1) b d))
  change φ (MvPolynomial.eval₂ (RingHom.id R) (fun i => (d i : R)) (F (classify (p + 1) b d))) = _
  simpa only [RingHom.comp_id, Function.comp_def, map_natCast] using he

def headMomentRecipe {p : ℕ} (b D : ℕ)
    (F : (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R)
    (tail : Fin p → ℕ) (M W : ℕ → R) : R :=
  BoundaryPolynomial.polynomialMomentRecipe
    (headPolynomial (F (Fin.cases none (classify p b tail))) tail) M W
    (fun n => profileRecipeValue b F (Fin.cases n tail)) D (b + 1)

lemma actual_profile_head_moment_recipe (P : PsiTheory) (p K b D : ℕ)
    (F : (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R)
    (hdegree : ∀ σ, (F σ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (p + 1) → ℕ,
      profileCoefficient P Y (List.ofFn d) K = MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (F (classify (p + 1) b d)))
    (tail : Fin p → ℕ) (M W : ℕ → R) (w : ℝ → ℕ → ℝ)
    (hm : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D →
      HasSum (fun n : ℕ => (n : ℝ) ^ k * w Y n) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ n : ℕ, n < b + 1 → w Y n = (φ Y) (W n)) :
    ∀ Y ∈ Icc (0 : ℝ) y₀,
      HasSum (fun n : ℕ => w Y n * profileCoefficient P Y (n :: List.ofFn tail) K)
        ((φ Y) (headMomentRecipe b D F tail M W)) := by
  intro Y hY
  let Q : Polynomial R := headPolynomial (F (Fin.cases none (classify p b tail))) tail
  apply BoundaryPolynomial.polynomialMomentRecipe_hasSum (φ Y) Q M W
    (fun n => profileRecipeValue b F (Fin.cases n tail)) D (b + 1)
    ((headPolynomial_degree _ _).trans (hdegree _)) (w Y) _ (hm Y hY) (hw Y hY)
  · intro n hn
    have hval := hactual Y hY (Fin.cases n tail)
    rw [profileRecipeValue_eval]
    simpa only [List.ofFn_succ, Fin.cases_zero, Fin.cases_succ] using hval
  · intro n hn
    have hval := hactual Y hY (Fin.cases n tail)
    rw [classify_large_head b n tail (by omega)] at hval
    rw [Polynomial.eval_map]
    change profileCoefficient P Y (n :: List.ofFn tail) K = Polynomial.eval₂ (φ Y) (n : ℝ) Q
    rw [headPolynomial_eval₂]
    have hv : (fun i : Fin (p + 1) => ((Fin.cases n tail i : ℕ) : ℝ)) =
        Fin.cases (n : ℝ) (fun i => (tail i : ℝ)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    simpa only [Q, List.ofFn_succ, Fin.cases_zero, Fin.cases_succ, hv] using hval
end WP.HigherOrder.JointBoundary
