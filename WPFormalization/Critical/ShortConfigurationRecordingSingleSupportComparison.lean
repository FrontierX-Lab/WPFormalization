import WPFormalization.External.ShortSingleCurveMinimalityGeometry
noncomputable section
universe u v w
namespace WP.Critical.ShortConfiguration
open Set WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open WP.External.ShortSupportingPieceGeometry WP.External.ShortSingleCurveMinimalityGeometry

lemma singleCurve_minimal_image_eq_supporting_piece {P:WP.PsiTheory}
    {G:WeilPeterssonGeometry.{u,v} P} {H:HyperbolicCurveGeometry.{u,v,w} G}
    (A:AmbientRealization H)
    (hcomplete:∀g n X,(A.model g n X).surface.domain=univ)
    (S:SingleCurvePieceClassics A) (M:SingleCurveMinimalityClassics A hcomplete S)
    {g n:ℕ} (hg:WP.Stable g n) (X:G.Moduli g n (fun _=>0))
    (γ:H.Primitive g n X) (hns:¬H.simple γ)
    (Q:SupportingPieceData (A.model g n X) {A.primitiveEquiv g n X γ})
    (D:IntrinsicRegionData (A.model g n X) (S.piece g n hg X γ hns).piece)
    (BD:IntrinsicBoundaryData (A.model g n X) (S.piece g n hg X γ hns).piece) :
    (S.piece g n hg X γ hns).piece.point ''
        intrinsicInterior (S.piece g n hg X γ hns).piece.model=
      Q.piece.point '' intrinsicInterior Q.piece.model := by
  apply Set.Subset.antisymm
  · exact M.minimal g n hg X γ hns Q.piece Q.region Q.boundary
      (Q.contains _ (by simp))
  · apply Q.minimal (S.piece g n hg X γ hns).piece D BD
    intro δ hδ
    have he:δ=A.primitiveEquiv g n X γ:=by simpa using hδ
    subst δ
    exact (S.piece g n hg X γ hns).contains
end WP.Critical.ShortConfiguration
