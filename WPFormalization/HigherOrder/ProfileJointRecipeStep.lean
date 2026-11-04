import WPFormalization.HigherOrder.FirstAdjacentJointRecipe
import WPFormalization.HigherOrder.ProfileJointStep
/-! The full actual next-profile step of the joint finite-data induction. Strictly lower actual profile/cusp/genus recipes plus the displayed finite kernel data construct a joint polynomial for the canonical order-k+1 coefficient, with degree at most D+2. The paper boundary cutoffs are supplied separately; the all-order induction is not an input theorem. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open Set
open JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma actual_profile_joint_recipe_step (P : PsiTheory) (m k b B D : ℕ)
    (hBH : 2 * b + 2 ≤ B) (hBS : b + (3 * (k + 1)) / 2 + 2 ≤ B)
    (F : ∀ q : ℕ, ℕ → (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ q i, i < k + 1 → ∀ τ, (F q i τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ q i, i < k + 1 → ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ v : Fin (q + 1) → ℕ,
      profileCoefficient P Y (List.ofFn v) i =
        MvPolynomial.eval₂ (φ Y) (fun j => (v j : ℝ)) (F q i (classify (q + 1) b v)))
    (A : R) (c g : ℕ → ℕ → R)
    (hA : ∀ Y ∈ Icc (0 : ℝ) y₀, (φ Y) A = WP.A Y)
    (hc : ∀ q ≥ 1, ∀ i < k + 1, ∀ Y ∈ Icc (0 : ℝ) y₀, cuspCoefficient P Y q i = (φ Y) (c q i))
    (hg : ∀ q ≥ 1, ∀ i < k + 1, ∀ Y ∈ Icc (0 : ℝ) y₀, genusCoefficient P Y q i = (φ Y) (g q i))
    (κ : ThetaPolynomial ((3 * (k + 1)) / 2 + 1) →+* R)
    (hκ : ∀ Y ∈ Icc (0 : ℝ) y₀, (φ Y).comp κ =
      MvPolynomial.eval (fun i : Fin ((3 * (k + 1)) / 2 + 2) => theta Y i.val))
    (M W : ℕ → R)
    (hm : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ j : ℕ, j ≤ D + 1 →
      HasSum (fun l : ℕ => (l : ℝ) ^ j * weight Y l) ((φ Y) (M j)))
    (hw : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ l : ℕ, l < B + 1 → weight Y l = (φ Y) (W l)) :
    ∃ Q : (Fin (m + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 1)) R,
      (∀ σ, (Q σ).totalDegree ≤ D + 2) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (m + 1) → ℕ,
        profileCoefficient P Y (List.ofFn d) (k + 1) =
          MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (Q (classify (m + 1) B d)) := by
  obtain ⟨Qfirst, hdegreeFirst, hactualFirst⟩ := actual_first_adjacent_joint_recipe
    P m (k + 1) b B D hBH hBS F hdegree φ hactual A c g hA hc hg κ hκ M W hm hw
  obtain ⟨Q, hdegreeQ, hactualQ⟩ := canonical_profile_joint_recipe_of_first_adjacent
    P m k B (D + 1) φ Qfirst hdegreeFirst hactualFirst
  refine ⟨Q, ?_, hactualQ⟩
  intro σ
  exact (hdegreeQ σ).trans_eq (by omega)
end WP.HigherOrder.KernelFiniteData
