import WPFormalization.External.ShortFillingGeometry

/- Explicit sourced classic interface. No instance, axiom, sorry, or paper-specific conclusion.
The old regular-neighborhood / boundary-straightening construction is applied
inside an ACTUAL closed convex quotient with actual geodesic boundary.
HYP-SINGLE-FILLING, derived bordered scope approved by root for R30.
Hide Def4.10 / Lem4.11(2), printed21--22, has COMPLETE ambient scope.
NWX v3 Prop59, printed57--58 / Sect3 printed11--13, has CLOSED ambient scope.
The extension here uses the SAME regular-neighborhood/perimeter construction
inside the invariant closed convex lift of an actual geodesic-boundary quotient;
axial representatives remain in the closed convex lift and minimize length.
Hide Def4.9's bordered definition is NOT a proof of this extension.
No positive-boundary, waist, pants, filling or kernel-support field is present.
Exact derivation and primary-source audit: audit/pants-bordered-single-curve-classical-fields.md. -/
noncomputable section
universe u v
namespace WP.External.ShortBorderedSingleCurveGeometry
open Set HyperbolicPacking ShortFillingGeometry

/-- Only the actual containing intrinsic piece and its boundary budget.
No area bound, minimality, positive boundary count, pants classification,
waist inequality, cluster proper support or probabilistic statement is stored.
Formal intrinsic boundary circles are allowed to share an ambient trace. -/
structure SingleCurveBoundaryPieceData (B : BorderedGeometry.{u,v})
    (γ : B.curves.Primitive) where
  piece : IntrinsicPiece B
  contains : B.curves.trace γ ⊆ piece.point '' intrinsicInterior piece.model
  inside : piece.point '' intrinsicInterior piece.model ⊆ intrinsicInterior B
  frontier_image : frontier (piece.point '' intrinsicInterior piece.model) =
    ⋃ j, B.curves.trace (piece.primitiveProjection (piece.boundary.curve j))
  boundary_length_le : boundaryLength piece.boundary ≤ 2 * B.curves.length γ

/-- Generic OLD single-curve neighborhood surgery with geodesic straightening.
The actual boundary realization is mandatory; a primitive lying on the ambient
boundary is excluded explicitly by the actual interior containment premise. -/
structure BorderedSingleCurveBoundaryClassics (B : BorderedGeometry.{u,v})
    (R : BoundaryRealization B) where
  piece : ∀ γ : B.curves.Primitive, ¬ SimpleTrace B γ →
    B.curves.trace γ ⊆ intrinsicInterior B → SingleCurveBoundaryPieceData B γ

end WP.External.ShortBorderedSingleCurveGeometry
