import WPFormalization.External.ShortFillingGeometry
/- Actual realization companion under the existing HYP-INTRINSIC-PIECES license.
This DATA record does not assert existence for arbitrary partial IntrinsicPiece
records. Genuine actual S.piece/cut-piece creators must carry the data.
Sources: Martelli printed p11 (Riemannian volume form), p52 (boundary charts
and geodesic-boundary completion), pp80--81 (proper actual cusp ends);
Hide printed pp22--23 (actual open subsurfaces with formal boundary sides).
The two semantic equalities are derived ordinary consequences, not G.3
component identifications, selections, budgets, counts or probability inputs.
Exact source conditions: audit/short-intrinsic-region-classical-fields.md. -/
noncomputable section
universe u v
namespace WP.External.ShortIntrinsicRegionGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry

/- Proposed missing SEMANTIC DATA for the actual intrinsic completion of an
open geodesic subsurface. No existence theorem for an arbitrary partial record
is asserted. The actual S/actual cut-piece producers must carry this data. -/
structure IntrinsicRegionData (B:BorderedGeometry.{u,v}) (P:IntrinsicPiece B) : Prop where
  frontier_image : frontier (P.point '' intrinsicInterior P.model)=
    ⋃j,B.curves.trace (P.primitiveProjection (P.boundary.curve j))
  area_image : B.surface.area (P.point '' intrinsicInterior P.model)=P.model.surface.area univ

end WP.External.ShortIntrinsicRegionGeometry
