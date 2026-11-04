import WPFormalization.External.ShortLoopStraighteningGeometry
noncomputable section
universe u v
namespace WP.External.ShortBorderedLoopGeometry
open Set HyperbolicPacking ShortFillingGeometry ShortLoopStraighteningGeometry

/- Stage-one generic classical data approved by the root source audit on
2026-11-01. No constructed instance, sorry, axiom, or paper result.
Generic convex geodesic-boundary straightening. The boundary realization is
actual, and no domain=univ premise is asserted for a bordered quotient.
Sources: Martelli Ch3 Thm1.13/Cor1.14 pp52--53 (convex universal cover),
Ch4 Prop1.14/Cor1.16 pp72--73 (axial class and minimal length), and
Farb--Margalit Version5 pp25,31--34 (simplicity and minimal position).
The same lift/axis proof stays in the invariant closed convex lift domain.
No primitive pants classification, filling, or boundary-length bound occurs.
-/
structure BorderedLoopStraighteningClassics (B : BorderedGeometry.{u,v})
    (R : BoundaryRealization B) where
  representative : ∀ f : ClosedLoop B.surface.Point,
    f.Simple → f.PositiveHomotopyLength →
      ∃ γ : B.curves.Primitive, (primitiveLoop B γ).UnorientedFreelyHomotopic f
  class_eq : ∀ γ δ : B.curves.Primitive,
    (primitiveLoop B γ).UnorientedFreelyHomotopic (primitiveLoop B δ) ↔ γ = δ
  length_minimal : ∀ (γ : B.curves.Primitive) (f : ClosedLoop B.surface.Point),
    (primitiveLoop B γ).UnorientedFreelyHomotopic f →
      ENNReal.ofReal (B.curves.length γ) ≤ f.length
  simple_representative : ∀ (γ : B.curves.Primitive) (f : ClosedLoop B.surface.Point),
    f.Simple → (primitiveLoop B γ).UnorientedFreelyHomotopic f → SimpleTrace B γ
  disjoint_representatives : ∀ (γ δ : B.curves.Primitive)
    (f g : ClosedLoop B.surface.Point), f.Simple → g.Simple →
    (primitiveLoop B γ).UnorientedFreelyHomotopic f →
    (primitiveLoop B δ).UnorientedFreelyHomotopic g → Disjoint f.trace g.trace →
      γ = δ ∨ Disjoint (B.curves.trace γ) (B.curves.trace δ)

/- TWO further low-level geometric facts, separately approved from the five
straightening fields. They directly support the actual intrinsic-piece bridge.
1) Martelli Ch4 Exercise1.11 p72 supports the trace/orientation/multiplicity
framework; primitive + inverse quotient removes orientation and multiplicity.
The exact interface is a derived geodesic-uniqueness combination, not a
claim that the exercise supplies a proved exact theorem in this API.
2) Convex geodesic boundary + uniqueness of a geodesic with its initial tangent:
a complete closed geodesic touching the frontier is that boundary geodesic.
Neither fact classifies simple curves on pants or supplies whole filling.
-/
structure PrimitiveBoundaryClassics (B : BorderedGeometry.{u,v})
    (R : BoundaryRealization B) : Prop where
  trace_injective : Function.Injective B.curves.trace
  interior_or_boundary : ∀ γ : B.curves.Primitive,
    B.curves.trace γ ⊆ intrinsicInterior B ∨ ∃ j, R.curve j = γ

end WP.External.ShortBorderedLoopGeometry
