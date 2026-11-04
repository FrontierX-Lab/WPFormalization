import WPFormalization.RandomGeometry.PantsMomentAsymptoticsIntegrals

/-! Pure physical-window integral definitions, independent of geometric moment
classification and of their later asymptotic estimates. -/
noncomputable section
namespace WP.RandomGeometry
open MeasureTheory

def pantsWindowVolumeIntegral (P : PsiTheory) (g m r : ℕ) (hr : r ≤ m)
    (I : Fin r → Set ℝ) : ℝ :=
  ∫ x : Fin r → ℝ in {x | ∀i, x i ∈ I i},
    boundaryVolumeModel P g m (activeBoundaryLengths hr x)*∏i, x i

end WP.RandomGeometry
