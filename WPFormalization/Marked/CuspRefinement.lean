import WPFormalization.Marked.FirstDegreeProof
import WPFormalization.Marked.DilatonRefinement

/-! The genuine refined cusp ratio, Eq. (7.7), for every fixed marking count.
The all-degree first-correction theorem is instantiated in the proved finite
canonical dilaton sum; no asymptotic profile hypothesis remains. -/
noncomputable section
namespace WP
lemma refined_cusp_proof (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Set.Icc (0 : ℝ) y₀,
      |(complexity g p : ℝ)*W P g p Y/W P g (p+1) Y-
        A Y*(1-dilatonBeta p Y/(complexity g p : ℝ))| ≤ C/(complexity g p : ℝ)^2 := by
  obtain ⟨Q,hQ,G,hprofile⟩ := first_degree_all_degrees_proof P (p+1) (by omega)
  exact refined_cusp_of_profile P p G Q hQ hprofile
end WP
