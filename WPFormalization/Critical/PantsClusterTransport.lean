import WPFormalization.Critical.PantsClusterDefinitions
import WPFormalization.External.PantsFamilyUniqueness

/-! Local full-spectrum transport under an actual pants isometry.  The
classical input gives only an isometry with its induced primitive transport;
equality of complete counting measures is proved here. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry MeasureTheory Set
open scoped ENNReal NNReal

def intrinsicMeasure (B : BorderedGeometry.{u,v}) : Measure ℝ≥0 :=
  Measure.sum (fun γ : B.curves.Primitive => Measure.dirac (Real.toNNReal (B.curves.length γ)))

lemma measure_eq_intrinsicMeasure (F : Family.{u,v}) (s : Waist) :
    measure F s = intrinsicMeasure (F.model s) :=
  measure_eq_intrinsic F s

lemma intrinsicMeasure_eq_of_isometry {B E : BorderedGeometry.{u,v}}
    (e : PantsIsometry B E) : intrinsicMeasure B = intrinsicMeasure E := by
  let μ : E.curves.Primitive → Measure ℝ≥0 :=
    fun γ => Measure.dirac (Real.toNNReal (E.curves.length γ))
  have he : (fun γ : B.curves.Primitive =>
      Measure.dirac (Real.toNNReal (B.curves.length γ))) = μ ∘ e.primitive := by
    funext γ
    dsimp only [Function.comp_def,μ]
    rw [e.length]
  unfold intrinsicMeasure
  rw [he]
  exact Measure.sum_comp_equiv e.primitive μ

lemma actual_pants_measure_eq_cluster (F : Family.{u,v}) (U : UniquenessClassics F)
    (B : BorderedGeometry.{u,v}) (hB : HasPantsTopology B)
    (R : BoundaryRealization B) (hboundary : B.boundaries = 1) (j : Fin B.boundaries) :
    intrinsicMeasure B = measure F
      ⟨B.curves.length (R.curve j),(B.curves.representative (R.curve j)).period_pos⟩ := by
  obtain ⟨e,he⟩ := U.isometry B hB R hboundary j
  rw [measure_eq_intrinsicMeasure]
  exact intrinsicMeasure_eq_of_isometry e

end WP.Critical.PantsCluster
