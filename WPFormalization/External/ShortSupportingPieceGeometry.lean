import WPFormalization.External.ShortIntrinsicRegionGeometry
import WPFormalization.External.ShortIntrinsicBoundaryGeometry
/-
Generic supporting subsurfaces of a finite connected closed-geodesic carrier.
Source: Burger–Iozzi–Parreau–Pozzetti, A structure theorem for geodesic currents
and length spectrum compactifications (5 December 2017), §3.2, printed 13–15.
The actual lifted-carrier hull equality and minimality are derived from the
construction on printed 14 and Definition 3.10 / Remark 3.11, not quotations
of a single numbered theorem. The complete finite-area ambient scope is
explicit; the single-simple (annular) carrier is excluded. No length/Euler
budget, recording, classification or counting result is an external field.
These are explicit classical interfaces without constructed instances; there
is no assertion that arbitrary partial IntrinsicPiece records have instances.
See audit/short-supporting-piece-classical-fields.md.
-/
noncomputable section
universe u v
namespace WP.External.ShortSupportingPieceGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry

def carrier (B:BorderedGeometry.{u,v}) (s:Finset B.curves.Primitive) : Set B.surface.Point :=
  ⋃γ∈s,B.curves.trace γ

def geodesicallyConvex (K:Set UpperHalfPlane) : Prop :=
  ∀a:ℝ→UpperHalfPlane,Isometry a→∀s t:ℝ,a s∈K→a t∈K→∀r∈uIcc s t,a r∈K

def closedGeodesicHull (W:Set UpperHalfPlane) : Set UpperHalfPlane :=
  sInter {K | IsClosed K ∧ geodesicallyConvex K ∧ W⊆K}

def liftedCarrierComponent (B:BorderedGeometry.{u,v}) (s:Finset B.curves.Primitive)
    (c:ConnectedComponents (B.surface.project ⁻¹' carrier B s)) : Set UpperHalfPlane :=
  {p | ∃hp:p∈B.surface.project ⁻¹' carrier B s,ConnectedComponents.mk ⟨p,hp⟩=c}

/- No budget/record data: genuine intrinsic completion of the canonical convex
support, with ordinary actual-region semantics and literal minimality. -/
structure SupportingPieceData (B:BorderedGeometry.{u,v}) (s:Finset B.curves.Primitive) where
  piece : IntrinsicPiece B
  region : IntrinsicRegionData B piece
  boundary : IntrinsicBoundaryData B piece
  contains : ∀γ∈s,B.curves.trace γ⊆piece.point '' intrinsicInterior piece.model
  liftComponent : ConnectedComponents (B.surface.project ⁻¹' carrier B s)
  image_eq_hull : piece.point '' intrinsicInterior piece.model=
    B.surface.project '' interior (closedGeodesicHull (liftedCarrierComponent B s liftComponent))
  minimal : ∀Q:IntrinsicPiece B,IntrinsicRegionData B Q→IntrinsicBoundaryData B Q→
    (∀γ∈s,B.curves.trace γ⊆Q.point '' intrinsicInterior Q.model)→
    piece.point '' intrinsicInterior piece.model⊆Q.point '' intrinsicInterior Q.model

structure SupportingPieceClassics (B:BorderedGeometry.{u,v})
    (hcomplete:B.surface.domain=univ) where
  support : ∀s:Finset B.curves.Primitive,s.Nonempty→IsPreconnected (carrier B s)→
    (2 ≤ s.card ∨ ∃γ∈s,¬SimpleTrace B γ)→SupportingPieceData B s

end WP.External.ShortSupportingPieceGeometry
