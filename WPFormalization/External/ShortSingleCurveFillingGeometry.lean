import WPFormalization.External.ShortFillingGeometry
import WPFormalization.External.ShortLoopStraighteningGeometry
/- Refinement of the existing HYP-SINGLE-FILLING classical interface.
Hide arXiv:2107.14555v4, printed p21 Definition4.9 and p22
Definition4.10/Lemma4.11(1). This is the stated local interior-loop consequence
of the actual disk/peripheral-cylinder complement, not a definition claimed
equivalent to the full filling topology. The same actual piece choice and an
explicit complete-ambient hypothesis are retained; no instance is asserted.
Full conditions: audit/short-single-curve-filling-classical-fields.md. -/
noncomputable section
universe u v w
namespace WP.External.ShortSingleCurveFillingGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry

/- This is a precise local CONSEQUENCE of the literal disk/peripheral-cylinder
complement in Hide Def4.9. It does not pretend to define the full topological
filling construction or classify a piece from its numerical labels. -/
def InteriorFilling (B:BorderedGeometry.{u,v}) (γ:B.curves.Primitive)
    (d:SingleCurvePieceData B γ) : Prop :=
  ∃β:d.piece.model.curves.Primitive,
    d.piece.primitiveProjection β=γ ∧
    d.piece.model.curves.trace β⊆intrinsicInterior d.piece.model ∧
    ∀l:ClosedLoop d.piece.model.surface.Point,
      l.Simple→l.PositiveHomotopyLength→l.trace⊆intrinsicInterior d.piece.model→
      Disjoint l.trace (d.piece.model.curves.trace β)→
      ∃j:Fin d.piece.model.boundaries,
        l.UnorientedFreelyHomotopic (primitiveLoop d.piece.model (d.piece.boundary.curve j))

/- Only the same actual complete cusped ambient family as Hide. The existing
piece constructor is fixed by S; no arbitrary new choice of a containing piece
can satisfy this interface by renaming an arbitrary predicate "filling". -/
structure SingleCurveFillingClassics {P:WP.PsiTheory}
    {G:WeilPeterssonGeometry.{u,v} P} {H:HyperbolicCurveGeometry.{u,v,w} G}
    (A:AmbientRealization H)
    (hcomplete:∀g n (X:G.Moduli g n (fun _=>0)),(A.model g n X).surface.domain=univ)
    (S:SingleCurvePieceClassics A) : Prop where
  fills : ∀g n (hstable:WP.Stable g n) (X:G.Moduli g n (fun _=>0))
    (γ:H.Primitive g n X) (hns:¬H.simple γ),
    InteriorFilling (A.model g n X) (A.primitiveEquiv g n X γ)
      (S.piece g n hstable X γ hns)

end WP.External.ShortSingleCurveFillingGeometry
