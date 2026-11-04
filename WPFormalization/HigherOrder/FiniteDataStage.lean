import WPFormalization.HigherOrder.FiniteDataEnvironment
import WPFormalization.HigherOrder.BoundarySummation
/-! The precise internal common-induction invariant in the actual finite ring Index J bJ, with all positive-arity profile certificates and current positive-marking scalar recipes. Only its genuine zero-order inhabitant is asserted here. A literal list recipe evaluates a joint certificate for use by the current scalar step. No all-order inhabitant or external paper assumption is declared. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open Set
open JointBoundary

def FiniteDataStage (P : PsiTheory) (J k : ℕ) : Prop :=
  ∃ F : ∀ q : ℕ, (Fin (q + 1) → Option (Fin (boundaryCutoff k + 1))) →
      MvPolynomial (Fin (q + 1)) (DataPolynomial J),
  ∃ c g : ℕ → DataPolynomial J,
    (∀ q σ, (F q σ).totalDegree ≤ 2 * k) ∧
    (∀ q, ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (q + 1) → ℕ,
      profileCoefficient P Y (List.ofFn d) k =
        MvPolynomial.eval₂ (dataEval J Y).toRingHom (fun i => (d i : ℝ))
          (F q (classify (q + 1) (boundaryCutoff k) d))) ∧
    (∀ p ≥ 1, ∀ Y ∈ Icc (0 : ℝ) y₀, cuspCoefficient P Y p k = dataEval J Y (c p)) ∧
    (∀ p ≥ 1, ∀ Y ∈ Icc (0 : ℝ) y₀, genusCoefficient P Y p k = dataEval J Y (g p))

lemma finiteDataStage_zero (P : PsiTheory) (J : ℕ) : FiniteDataStage P J 0 := by
  refine ⟨fun _ _ => 1, fun _ => 1, fun _ => 1, ?_, ?_, ?_, ?_⟩
  · intro q σ
    simp
  · intro q Y hY d
    simp only [profileCoefficient_zero, MvPolynomial.eval₂_one]
  · intro p hp Y hY
    simp only [cuspCoefficient_zero, map_one]
  · intro p hp Y hY
    simp only [genusCoefficient_zero, map_one]
end WP.HigherOrder.KernelFiniteData

namespace WP.HigherOrder.JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def listRecipe (B : ℕ)
    (F : ∀ q : ℕ, (Fin (q + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (q + 1)) R) :
    List ℕ → R
  | [] => 0
  | t :: tail =>
      let d : Fin (tail.length + 1) → ℕ := Fin.cases t tail.get
      MvPolynomial.eval (fun i => (d i : R)) (F tail.length (classify (tail.length + 1) B d))

lemma listRecipe_actual_eval (P : PsiTheory) (k B : ℕ)
    (F : ∀ q : ℕ, (Fin (q + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (q + 1)) R)
    (φ : R →+* ℝ) (Y : ℝ)
    (hactual : ∀ q, ∀ v : Fin (q + 1) → ℕ,
      profileCoefficient P Y (List.ofFn v) k =
        MvPolynomial.eval₂ φ (fun i => (v i : ℝ)) (F q (classify (q + 1) B v)))
    (d : List ℕ) (hd : 1 ≤ d.length) :
    profileCoefficient P Y d k = φ (listRecipe B F d) := by
  cases d with
  | nil => simp at hd
  | cons t tail =>
    have hh := hactual tail.length (Fin.cases t tail.get)
    have he : List.ofFn (Fin.cases t tail.get) = t :: tail := by
      simp only [List.ofFn_succ, Fin.cases_zero, Fin.cases_succ, List.ofFn_get]
    rw [he] at hh
    rw [listRecipe, map_eval_nat]
    exact hh
end WP.HigherOrder.JointBoundary
