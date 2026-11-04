import WPFormalization.Critical.PantsClusterGenericSimple
import WPFormalization.Critical.ShortConfigurationRecordingLoopHomotopy

/-! The geodesic simple classification also controls actual simple positive
homotopy classes. This is a boundary-parallel classification only, not a claim
that an arbitrary contained curve fills the whole pants. -/
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry
open WP.External.PlanarJordanGeometry WP.External.PlanarRegionGeometry
open WP.External.ShortBorderedPeripheralGeometry

lemma actual_pants_simple_loop_boundary_parallel (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) (R : BoundaryRealization B) (hb : B.boundaries = 1)
    (BC : PrimitiveBoundaryClassics B R) (LS : BorderedLoopStraighteningClassics B R)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics B R) (f : ClosedLoop B.surface.Point)
    (hf : f.Simple) (hpos : f.PositiveHomotopyLength) (j : Fin B.boundaries) :
    f.UnorientedFreelyHomotopic (primitiveLoop B (R.curve j)) := by
  obtain ⟨γ,hγ⟩ := LS.representative f hf hpos
  have hs := LS.simple_representative γ f hf hγ
  have he := (actual_pants_simple_iff_boundary B hp R hb BC LS J PC PP γ j).mp hs
  subst γ
  exact WP.Critical.ShortConfiguration.ClosedLoop.unoriented_symm hγ

end WP.Critical.PantsCluster
