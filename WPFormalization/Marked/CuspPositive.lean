import WPFormalization.Marked.CuspFromProfile
import WPFormalization.Statements.QuadraticProfile
/-! The original positive-marking cusp estimate from the proved quadratic profile. -/
noncomputable section
open Set Filter
namespace WP
lemma marked_cusp_proof (P : PsiTheory) (p : ℕ) (hp : 1≤p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |(complexity g p : ℝ)*W P g p Y/W P g (p+1) Y-A Y|≤C/g := by
  obtain ⟨Q,hQ,hquad⟩ := quadratic_profile P (p+1) (by omega)
  obtain ⟨C,hC,hbound⟩ := cusp_estimate_of_quadratic P p Q hQ hquad
  refine ⟨C,hC,1,?_⟩
  intro g hg Y hY
  exact hbound g hg (by unfold Stable; omega) Y hY
end WP
