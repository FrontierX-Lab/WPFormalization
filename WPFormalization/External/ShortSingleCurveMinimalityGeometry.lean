import WPFormalization.External.ShortSupportingPieceGeometry
/- Minimal actual supporting image of the SAME genuine Hide creator S.
Source: Hide Def4.10 printed22, compared with BIPP §3.2 printed13–15 and
Remark3.11 for a nonsimple singleton carrier. Explicit complete ambient,
no arbitrary S instances and no pants/recording/budget/count field.
This does not identify weak InteriorFilling with full topological filling.
Source/conditions: audit/short-single-curve-minimality-classical-fields.md. -/
noncomputable section
universe u v w
namespace WP.External.ShortSingleCurveMinimalityGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open WP.External.ShortSupportingPieceGeometry

/- Companion of the SAME genuine Hide creator S, with actual complete
ambient. No instance for arbitrary S records is claimed. This is only the
ordinary minimal supporting-image semantics of that old construction. -/
structure SingleCurveMinimalityClassics {P:WP.PsiTheory}
    {G:WeilPeterssonGeometry.{u,v} P} {H:HyperbolicCurveGeometry.{u,v,w} G}
    (A:AmbientRealization H)
    (hcomplete:∀g n X,(A.model g n X).surface.domain=univ)
    (S:SingleCurvePieceClassics A) : Prop where
  minimal : ∀g n (hg:WP.Stable g n) (X:G.Moduli g n (fun _=>0))
    (γ:H.Primitive g n X) (hns:¬H.simple γ),
    ∀Q:IntrinsicPiece (A.model g n X),
      IntrinsicRegionData (A.model g n X) Q→
      IntrinsicBoundaryData (A.model g n X) Q→
      (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
        Q.point '' intrinsicInterior Q.model→
      (S.piece g n hg X γ hns).piece.point ''
          intrinsicInterior (S.piece g n hg X γ hns).piece.model⊆
        Q.point '' intrinsicInterior Q.model

end WP.External.ShortSingleCurveMinimalityGeometry
