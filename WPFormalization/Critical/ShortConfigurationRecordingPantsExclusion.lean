import WPFormalization.Critical.ShortConfigurationIntrinsicSimpleLift
import WPFormalization.Critical.ShortConfigurationRecordingPieceCut
import WPFormalization.Critical.PantsClusterGenericSimple
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.PantsCluster
open WP.External.ShortBorderedLoopGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.Critical.PantsCluster

lemma actual_simple_not_contained_pants_piece {B:BorderedGeometry.{u,v}}
    (Q:IntrinsicPiece B) (D:IntrinsicRegionData B Q)
    (hp:HasPantsTopology Q.model) (hb:Q.model.boundaries=1)
    (BC:PrimitiveBoundaryClassics Q.model Q.boundary)
    (LS:BorderedLoopStraighteningClassics Q.model Q.boundary)
    (J:PlanarJordanClassics) (PC:PlanarRegionClassics)
    (PP:BorderedPeripheralClassics Q.model Q.boundary)
    (γ:B.curves.Primitive) (hsimple:SimpleTrace B γ) :
    ¬B.curves.trace γ⊆Q.point '' intrinsicInterior Q.model := by
  intro htrace
  obtain ⟨β,hproj,hs,hℓ⟩:=intrinsicPiece_exists_simple_lift Q γ htrace hsimple
  let j:Fin Q.model.boundaries:=⟨0,by omega⟩
  have he:β=Q.boundary.curve j:=
    (actual_pants_simple_iff_boundary Q.model hp Q.boundary hb BC LS J PC PP β j).mp hs
  rw [he] at hproj
  obtain ⟨p,hpγ⟩:=primitive_trace_nonempty B γ
  have hU:p∈Q.point '' intrinsicInterior Q.model:=htrace hpγ
  have hf:p∈frontier (Q.point '' intrinsicInterior Q.model):=by
    rw [D.frontier_image]
    exact Set.mem_iUnion.mpr ⟨j,hproj.symm ▸ hpγ⟩
  exact hf.2 (Q.image_open.interior_eq.symm ▸ hU)
end WP.Critical.ShortConfiguration
