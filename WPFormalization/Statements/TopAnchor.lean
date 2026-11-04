import WPFormalization.Coefficients.TopAnchorProof
noncomputable section
namespace WP

/- Blueprint label(s): eq:C18
Paper v3: 13.18 [PDF 55]
Status: CONDITIONALLY_PROVED; PsiTheory and classical one_point remain
-/
@[blueprint "eq:C18"]
theorem top_anchor (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g) :
    mixedJ P g (3*g-3)/mixedJ P g (3*g-2) = (12*(g : ℝ)^2-12*g+5)/5 ∧
    boundaryA P g (3*g-3)/boundaryA P g (3*g-2) =
      2*Real.pi^2*(12*(g : ℝ)^2-12*g+5)/(5*(6*(g : ℝ)-3)) := by
  exact ⟨top_anchor_mixedJ_ratio P g hg, top_anchor_boundaryA_ratio P g hg⟩

end WP
