import WPFormalization.External.ShortIntrinsicRegionGeometry
import WPFormalization.External.ShortIntrinsicBoundaryGeometry
/-
Uniqueness of the actual metric completions of the same open geodesic
subsurface. Source: Martelli, Hyperbolic geometry (2014), printed 52–54,
especially uniqueness of Riemannian completion on printed 54, with the cusp
scope on printed 80–81. This is a scoped companion of the same actual
intrinsic-piece and cut creators, not an instance for arbitrary partial data.
No component is selected and no numeric topology or paper event is returned.
See audit/short-intrinsic-completion-classical-fields.md.
-/
noncomputable section
universe u v w z
namespace WP.External.ShortIntrinsicCompletionGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry

/- Actual uniqueness of the two intrinsic metric completions of the SAME
open geodesic subsurface. No numeric topology or paper event is a field. -/
structure SameImageCompletionData {B:BorderedGeometry.{u,v}} (P Q:IntrinsicPiece B) where
  point : P.model.surface.Point ≃ᵢ Q.model.surface.Point
  ambient : ∀p,Q.point (point p)=P.point p
  boundary : ∀p,p∈intrinsicBoundary P.model ↔ point p∈intrinsicBoundary Q.model

/- Scoped companion of this same genuine Q and actual cut creator R.
It asserts no instance for arbitrary partial input records. -/
structure CutCompletionRealization {P:WP.PsiTheory}
    {G:WeilPeterssonGeometry.{u,v} P} {H:HyperbolicCurveGeometry.{u,v,w} G}
    {A:AmbientRealization H} {T:MulticurveTopology.{u,v,w,z} G H}
    {g n k:ℕ} {o:T.Orbit g n k} {X:G.Moduli g n (fun _=>0)}
    {κ:Fin k→H.Primitive g n X} {hκ:T.orbitMem o X κ}
    (hcomplete:(A.model g n X).surface.domain=univ)
    (Q:IntrinsicPiece (A.model g n X))
    (D:IntrinsicRegionData (A.model g n X) Q)
    (BD:IntrinsicBoundaryData (A.model g n X) Q)
    (R:CutComponentRealization A T o X κ hκ)
    (AR:∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (BR:∀c,IntrinsicBoundaryData (A.model g n X) (R.piece c)) : Prop where
  completion : ∀c,(Q.point '' intrinsicInterior Q.model)=
      (R.piece c).point '' intrinsicInterior (R.piece c).model→
    Nonempty (SameImageCompletionData Q (R.piece c))

end WP.External.ShortIntrinsicCompletionGeometry
