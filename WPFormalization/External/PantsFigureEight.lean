import WPFormalization.External.PantsFamily
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! The classical figure-eight on a two-cusp pair of pants. -/
noncomputable section
universe u v
namespace WP.External.PantsCluster

/-- Rivin, Advances in Mathematics 231 (2012), Theorem 1.3 (Theorem 2,
Eq. (1) in the author's preprint arXiv:0901.2543), with cusp lengths 0,0.
The geodesic represented by a⁻¹b has one transverse double point, is
primitive, and is distinct from the boundary class. The latter two facts
also follow from the reduced word a⁻¹b in the free pants group.
This explicit classical input asserts no cluster-count or probability fact. -/
def FigureEightClassics (F : Family.{u, v}) : Prop :=
  ∀ s : Waist, ∃ γ : F.Primitive, γ ≠ F.waistClass ∧
    F.length s γ = 2 * Real.arcosh (2 + Real.cosh (s.val / 2))
end WP.External.PantsCluster
