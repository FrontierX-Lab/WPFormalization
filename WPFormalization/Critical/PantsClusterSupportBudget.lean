import WPFormalization.Critical.PantsClusterGenericSimple

/-! A genuine containing intrinsic piece with at least one geodesic boundary
already suffices for the desired waist budget on an actual pants. Existence and
boundary nonemptiness of such a piece are deliberately NOT assumed as fields
or claimed proved here. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry
open WP.External.PlanarJordanGeometry WP.External.PlanarRegionGeometry
open WP.External.ShortBorderedPeripheralGeometry

lemma actual_pants_piece_boundary_projection (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) (R : BoundaryRealization B) (hb : B.boundaries = 1)
    (BC : PrimitiveBoundaryClassics B R) (LS : BorderedLoopStraighteningClassics B R)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics B R) (E : IntrinsicPiece B)
    (i : Fin E.model.boundaries) (j : Fin B.boundaries) :
    E.primitiveProjection (E.boundary.curve i) = R.curve j :=
  (actual_pants_simple_iff_boundary B hp R hb BC LS J PC PP _ j).mp (E.boundary_simple i)

lemma actual_pants_waist_budget_of_actual_piece (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) (R : BoundaryRealization B) (hb : B.boundaries = 1)
    (BC : PrimitiveBoundaryClassics B R) (LS : BorderedLoopStraighteningClassics B R)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics B R) (γ : B.curves.Primitive)
    (d : SingleCurvePieceData B γ) (hd : 0 < d.piece.model.boundaries)
    (j : Fin B.boundaries) : B.curves.length (R.curve j) ≤ 2 * B.curves.length γ := by
  let i : Fin d.piece.model.boundaries := ⟨0,hd⟩
  have heq := actual_pants_piece_boundary_projection B hp R hb BC LS J PC PP d.piece i j
  calc
    B.curves.length (R.curve j) =
        d.piece.model.curves.length (d.piece.boundary.curve i) := by
      rw [←d.piece.length_preserved,heq]
    _ ≤ boundaryLength d.piece.boundary := by
      unfold boundaryLength
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun b => d.piece.model.curves.length (d.piece.boundary.curve b))
        (fun b _ => (d.piece.model.curves.representative (d.piece.boundary.curve b)).period_pos.le)
        (Finset.mem_univ i)
    _ ≤ 2 * B.curves.length γ := d.boundary_length_le

lemma canonical_waist_budget_of_actual_piece (F : Family.{u,v}) (s : Waist)
    (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) (d : SingleCurvePieceData (F.model s) (F.marking s γ))
    (hd : 0 < d.piece.model.boundaries) : s.val ≤ 2 * F.length s γ := by
  have h := actual_pants_waist_budget_of_actual_piece (F.model s) ⟨F.topology s,F.topological_boundary s⟩
    (F.boundary s) (F.boundaries s) BC LS J PC PP (F.marking s γ) d hd (F.waist s)
  rwa [F.waist_length] at h

end WP.Critical.PantsCluster
