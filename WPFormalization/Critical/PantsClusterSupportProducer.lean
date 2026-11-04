import WPFormalization.External.ShortBorderedSingleCurveGeometry
import WPFormalization.Critical.PantsClusterProperSupport
import WPFormalization.Critical.ShortConfigurationRecordingPositiveBoundary

/-! The actual pants support estimate is a LOCAL theorem. Its only added
classic input is the sourced generic RN/boundary-straightening construction;
the actual pants classification, positive boundary count and waist budget
are proved locally, rather than fields of that interface. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
open scoped NNReal ENNReal
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry
open WP.External.PlanarJordanGeometry WP.External.PlanarRegionGeometry
open WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortBorderedSingleCurveGeometry
open WP.Critical.ShortConfiguration Set MeasureTheory

lemma canonical_waist_le_twice_length (F : Family.{u,v}) (s : Waist)
    (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) : s.val ≤ 2 * F.length s γ := by
  classical
  by_cases hγ : γ = F.waistClass
  · subst γ
    rw [F.length_waist]
    exact le_mul_of_one_le_left s.property.le (by norm_num)
  · have hn := canonical_nonwaist_not_simple F s BC LS J PC PP γ hγ
    have hi := canonical_nonwaist_trace_interior F s BC γ hγ
    let d := SC.piece (F.marking s γ) hn hi
    have hne : (d.piece.point '' intrinsicInterior d.piece.model).Nonempty :=
      (primitive_trace_nonempty (F.model s) (F.marking s γ)).mono d.contains
    have hd := actual_pants_intrinsic_piece_boundaries_pos (F.model s)
      ⟨F.topology s,F.topological_boundary s⟩ (F.boundary s) (F.waist s)
      d.piece hne d.inside d.frontier_image
    exact canonical_waist_budget_of_boundary_sum F s BC LS J PC PP γ d.piece hd
      d.boundary_length_le

theorem canonical_measure_prefix_eq_zero (F : Family.{u,v}) (s : Waist)
    (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (L : ℝ≥0) (hs : 2 * (L : ℝ) < s.val) : measure F s (Iic L) = 0 := by
  rw [measure_prefix_eq_zero_iff]
  intro γ
  have h := canonical_waist_le_twice_length F s BC LS J PC PP SC γ
  linarith

/-- Exact proper-prefix interface used by the actual cluster-measure and
Poisson-Laplace consumers. No support estimate remains as a premise. -/
theorem canonical_prefix_cutoff (F : Family.{u,v})
    (BC : ∀s,PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : ∀s,BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀s,BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀s,BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s)) :
    ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val → measure F s (Iic L)=0 := by
  intro s L hs
  exact canonical_measure_prefix_eq_zero F s (BC s) (LS s) J PC (PP s) (SC s) L hs

end WP.Critical.PantsCluster
