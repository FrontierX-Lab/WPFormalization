import WPFormalization.External.ShortSupportingPieceGeometry
import WPFormalization.Critical.ShortConfigurationRecordingEssentialBoundary
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
/- Actual creator semantics of the BIPP §3.2 construction, printed14:
surviving RN boundary sides and the carrier-induced fundamental-group
surjection. Explicit scoped DATA of the same genuine creators; no arbitrary
partial-data instance, numeric budget, recording or counting field.
Full conditions and source: audit/short-supporting-construction-classical-fields.md. -/
noncomputable section
universe u v z
namespace WP.External.ShortSupportingConstructionGeometry
open Set Topology WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortRegularNeighborhoodGeometry WP.External.ShortLoopStraighteningGeometry
open WP.Critical.ShortConfiguration
/- Companion DATA of the same genuine supporting/RN creators. The actual
formal sides that survive disk/cusp filling and straightening retain distinct
original RN boundary cycles, including duplicate ambient geodesic images. -/
structure SupportingBoundaryRealization {B:BorderedGeometry.{u,v}}
    (Q:IntrinsicPiece B) (N:EmbeddedNetwork.{u,0} B.surface.Point)
    (D:NeighborhoodData N) (C:WP.External.FiniteCyclicIntervalGeometry.Classics) where
  cycle : Fin Q.model.boundaries ↪ D.rotation.BoundaryCycle N
  homotopic : ∀j,(primitiveLoop B (Q.primitiveProjection (Q.boundary.curve j))).UnorientedFreelyHomotopic
    (frontierCycle B N D C (cycle j))

/- The actual graph carrier map into this same supporting completion. The
map commutes with the actual ambient inclusion, and its induced fundamental
group map is surjective. This is the literal Γ_n=π1(Σ_n) construction semantics,
not a bound on a paper recording. -/
structure SupportingCarrierRealization {B:BorderedGeometry.{u,v}}
    (Q:IntrinsicPiece B) (N:EmbeddedNetwork.{u,0} B.surface.Point) where
  point : C(N.support,Q.model.surface.Point)
  ambient : ∀p,Q.point (point p)=p.val
  interior : ∀p,point p∈intrinsicInterior Q.model
  surjective : ∀p:N.support,Function.Surjective (FundamentalGroup.map point p)


end WP.External.ShortSupportingConstructionGeometry
