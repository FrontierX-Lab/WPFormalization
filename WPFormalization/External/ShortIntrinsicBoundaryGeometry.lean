import WPFormalization.External.ShortIntrinsicRegionGeometry
/- Same actual-realization DATA under the already reviewed classical license.
Derived ordinary cut/surface or geodesic-boundary semantics, not a verbatim
source record and not an existence theorem for arbitrary partial records.
The actual creator carries this data. No G.3 recording, selection, budget,
count or expectation conclusion is a field.
Exact conditions and primary sources: audit/short-intrinsic-boundary-classical-fields.md. -/
noncomputable section
universe u v
namespace WP.External.ShortIntrinsicBoundaryGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry

/- Additional ordinary actual-subsurface boundary DATA, not a theorem that
arbitrary partial IntrinsicPiece records have a geometric realization. -/
structure IntrinsicBoundaryData (B:BorderedGeometry.{u,v}) (P:IntrinsicPiece B) : Prop where
  disjoint : ∀i j:Fin P.model.boundaries,
    P.primitiveProjection (P.boundary.curve i)≠P.primitiveProjection (P.boundary.curve j)→
    Disjoint (B.curves.trace (P.primitiveProjection (P.boundary.curve i)))
      (B.curves.trace (P.primitiveProjection (P.boundary.curve j)))
end WP.External.ShortIntrinsicBoundaryGeometry
