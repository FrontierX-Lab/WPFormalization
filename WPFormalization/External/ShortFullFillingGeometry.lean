import VersoBlueprint.Attribute
import WPFormalization.External.ShortComplementaryRegionGeometry

/-! Literal complement formulation of filling, and the full filling clause of
Hide's classical construction (arXiv:2107.14555v4, printed pp.21--22,
Definition 4.9, Definition 4.10, Lemma 4.11(1)). This is separate from the
weaker interior-simple-loop consequence used elsewhere in this project.

No instance is asserted for an arbitrary containing-piece choice S. The
companion is scoped to the SAME genuine Hide creator. It assumes no pants
classification, recording, counting, or probabilistic estimate. -/
noncomputable section
universe u v w
namespace WP.External.ShortFullFillingGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortComplementaryRegionGeometry

def curveComplementComponent (B : BorderedGeometry.{u,v})
    (γ : B.curves.Primitive) (p : B.surface.Point) : Set B.surface.Point :=
  connectedComponentIn (B.curves.trace γ)ᶜ p

/- A boundary cylinder includes its actual geodesic boundary circle. Its
coordinates identify that circle with the zero end, so it retracts to the
actual boundary component rather than an arbitrary essential loop. -/
def IsBoundaryFillingCylinder (B : BorderedGeometry.{u,v})
    (R : BoundaryRealization B) (C : Set B.surface.Point) : Prop :=
  ∃ j : Fin B.boundaries, ∃ e : (LoopCircle × Ici (0 : ℝ)) ≃ₜ C,
    Set.range (fun z : LoopCircle => (e (z, ⟨0, by simp⟩)).val) =
      B.curves.trace (R.curve j)

/- A cusp cylinder has an actual proper cusp-end subregion. The closed
embedding in CuspEndBoundedBy rules out a cylinder around an omitted ordinary
surface point; no cusp number or freely chosen peripheral predicate is used. -/
def IsCuspFillingCylinder (B : BorderedGeometry.{u,v})
    (C : Set B.surface.Point) : Prop :=
  Nonempty ((LoopCircle × ℝ) ≃ₜ C) ∧
    ∃ f : ClosedLoop B.surface.Point, ∃ E : CuspEndBoundedBy f,
      Set.range E.map ⊆ C

def FullFilling (B : BorderedGeometry.{u,v}) (R : BoundaryRealization B)
    (γ : B.curves.Primitive) : Prop :=
  ∀ p : B.surface.Point, p ∉ B.curves.trace γ →
    Nonempty ((curveComplementComponent B γ p) ≃ₜ ℂ) ∨
      IsBoundaryFillingCylinder B R (curveComplementComponent B γ p) ∨
      IsCuspFillingCylinder B (curveComplementComponent B γ p)

@[blueprint "ext:short-filling"]
structure FullSingleCurveFillingClassics {P : WP.PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} {H : HyperbolicCurveGeometry.{u,v,w} G}
    (A : AmbientRealization H)
    (hcomplete : ∀ g n X, (A.model g n X).surface.domain = univ)
    (S : SingleCurvePieceClassics A) : Prop where
  fills : ∀ g n (hg : WP.Stable g n) (X : G.Moduli g n (fun _ => 0))
    (γ : H.Primitive g n X) (hns : ¬ H.simple γ),
    ∃ β : (S.piece g n hg X γ hns).piece.model.curves.Primitive,
      (S.piece g n hg X γ hns).piece.primitiveProjection β =
        A.primitiveEquiv g n X γ ∧
      (S.piece g n hg X γ hns).piece.model.curves.trace β ⊆
        intrinsicInterior (S.piece g n hg X γ hns).piece.model ∧
      FullFilling (S.piece g n hg X γ hns).piece.model
        (S.piece g n hg X γ hns).piece.boundary β

end WP.External.ShortFullFillingGeometry
