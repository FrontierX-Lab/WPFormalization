import WPFormalization.Marked.CuspFromProfile
import WPFormalization.Marked.SingleMarkingProfile
/-! Cusp estimates for all marking counts, including zero in the stable eventual range. -/
noncomputable section
open Set Filter
namespace WP
lemma marked_cusp_all_proof (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |(complexity g p : ℝ)*W P g p Y/W P g (p+1) Y-A Y|≤C/g := by
  exact marked_cusp_all_from_quadratic P (quadratic_profile_all_markings_proof P) p
lemma marked_cusp_zero_proof (P : PsiTheory) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |(complexity g 0 : ℝ)*W P g 0 Y/W P g 1 Y-A Y|≤C/g := by
  exact marked_cusp_all_proof P 0
end WP
