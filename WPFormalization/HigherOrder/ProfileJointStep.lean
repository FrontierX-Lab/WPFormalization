import WPFormalization.HigherOrder.PathPivotProjection
import WPFormalization.HigherOrder.BoundarySummation
import WPFormalization.HigherOrder.TriangularLocality
/-! A genuine first-coordinate adjacent certificate gives the next actual canonical profile certificate. Projection of beforeCoordinate supplies every path edge, finite-order locality identifies the actual previous jet, and the defined fixed path is summed exactly. Total degree increases by one; no current profile formula or arbitrary path compatibility is assumed. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open Set PowerSeries
open JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma canonical_profile_joint_recipe_of_first_adjacent (P : PsiTheory) (m k B D : ℕ)
    (φ : ℝ → R →+* ℝ)
    (Qfirst : (Fin (m + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 1)) R)
    (hdegree : ∀ σ, (Qfirst σ).totalDegree ≤ D)
    (hfirst : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (m + 1) → ℕ,
      adjacentCoefficient P Y (formalHierarchyJet P Y) (k + 1) 0 (List.ofFn d) =
        MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (Qfirst (classify (m + 1) B d))) :
    ∃ Q : (Fin (m + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 1)) R,
      (∀ σ, (Q σ).totalDegree ≤ D + 1) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (m + 1) → ℕ,
        profileCoefficient P Y (List.ofFn d) (k + 1) =
          MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (Q (classify (m + 1) B d)) := by
  let E : Fin (m + 1) → (Fin (m + 2) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 2)) R :=
    fun i σ => projectStratumPolynomial B (pathPivotProjection i) Qfirst σ
  have hE (i : Fin (m + 1)) (σ) : (E i σ).totalDegree ≤ D :=
    projectStratumPolynomial_degree B D _ Qfirst hdegree σ
  have hactual : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ i : Fin (m + 1), ∀ v : Fin (m + 2) → ℕ,
      adjacentCoefficient P Y (hierarchyJet P Y k) (k + 1) i.val
          (beforeCoordinate (List.ofFn (fun j => v j.succ)) i.val (v 0)) =
        MvPolynomial.eval₂ (φ Y) (fun j => (v j : ℝ)) (E i (classify (m + 2) B v)) := by
    intro Y hY i v
    have he := projectStratumPolynomial_actual_eval B (pathPivotProjection i) Qfirst (φ Y)
      (fun w => adjacentCoefficient P Y (formalHierarchyJet P Y) (k + 1) 0 (List.ofFn w)) (hfirst Y hY) v
    have hmove := adjacent_beforeCoordinate_project P Y (formalHierarchyJet P Y) (k + 1) i v
    have hsame := adjacentCoefficient_coeff_congr P Y (formalHierarchyJet P Y) (hierarchyJet P Y k)
      (k + 1) i.val (beforeCoordinate (List.ofFn (fun j => v j.succ)) i.val (v 0))
      (fun d => formalProfile_stage_agree P Y d k)
      (fun p => formalCusp_stage_agree P Y p k)
      (fun p => formalGenus_stage_agree P Y p k)
    exact hsame.symm.trans (hmove.trans he)
  refine ⟨fun σ => fixedPathPolynomial B B σ E, ?_, ?_⟩
  · intro σ
    exact fixedPathPolynomial_degree B B D σ E hE
  · exact actual_canonical_profile_path_recipe P (m + 1) k B B le_rfl E φ hactual
end WP.HigherOrder.KernelFiniteData
