import WPFormalization.Critical.ShortConfigurationRecordingPieceCut
import WPFormalization.Critical.PantsClusterDomain
import WPFormalization.Critical.PantsClusterConnected
/- Local positive-boundary argument for a genuine intrinsic image inside an
actual connected bordered surface: empty formal boundary gives empty actual
frontier, hence a nonempty clopen image equal to the whole ambient surface,
contradicting a point of the actual ambient boundary. No numeric pants
classification or additional geometric existence field is used. -/
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.PantsCluster
open WP.Critical.PantsCluster

lemma actual_intrinsic_piece_boundaries_pos (B:BorderedGeometry.{u,v})
    [PreconnectedSpace B.surface.Point] (Q:IntrinsicPiece B)
    (hne:(Q.point '' intrinsicInterior Q.model).Nonempty)
    (hinside:Q.point '' intrinsicInterior Q.model⊆intrinsicInterior B)
    (hfront:frontier (Q.point '' intrinsicInterior Q.model)=
      ⋃j,B.curves.trace (Q.primitiveProjection (Q.boundary.curve j)))
    (hboundary:(intrinsicBoundary B).Nonempty) : 0<Q.model.boundaries := by
  by_contra h
  have hz:Q.model.boundaries=0:=by omega
  have hf:frontier (Q.point '' intrinsicInterior Q.model)=∅:=by
    rw [hfront]
    ext p
    simp [hz]
  have hu:(Q.point '' intrinsicInterior Q.model)=univ:=
    (isClopen_iff_frontier_eq_empty.mpr hf).eq_univ hne
  obtain ⟨p,hp⟩:=hboundary
  have hi:p∈intrinsicInterior B:=hinside (hu.symm ▸ Set.mem_univ p)
  exact Set.disjoint_left.mp (intrinsic_interior_disjoint_boundary B) hi hp

lemma actual_pants_intrinsic_piece_boundaries_pos (B:BorderedGeometry.{u,v})
    (hp:HasPantsTopology B) (R:BoundaryRealization B) (j:Fin B.boundaries)
    (Q:IntrinsicPiece B)
    (hne:(Q.point '' intrinsicInterior Q.model).Nonempty)
    (hinside:Q.point '' intrinsicInterior Q.model⊆intrinsicInterior B)
    (hfront:frontier (Q.point '' intrinsicInterior Q.model)=
      ⋃j,B.curves.trace (Q.primitiveProjection (Q.boundary.curve j))) :
    0<Q.model.boundaries := by
  letI:=actual_pants_preconnectedSpace B hp
  apply actual_intrinsic_piece_boundaries_pos B Q hne hinside hfront
  obtain ⟨p,hp⟩:=primitive_trace_nonempty B (R.curve j)
  refine ⟨p,?_⟩
  rw [←R.cover]
  exact Set.mem_iUnion.mpr ⟨j,hp⟩
end WP.Critical.ShortConfiguration
