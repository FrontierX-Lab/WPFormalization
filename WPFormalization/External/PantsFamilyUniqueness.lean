import WPFormalization.External.PantsFamily

/-! Stage-one classical interface HYP-PANTS-UNIQUENESS, approved by the root
source audit on 2026-11-01. Generic uniqueness of an actual two-punctured disk with
geodesic boundary, with the primitive-class transport induced by the isometry.
This is not a cluster embedding, filling/support or stochastic hypothesis. -/
noncomputable section
universe u v
namespace WP.External.PantsCluster
open HyperbolicPacking ShortFillingGeometry Set

def HasPantsTopology (B : BorderedGeometry.{u,v}) : Prop :=
  ∃ e : B.surface.Point ≃ₜ TwicePuncturedDisk,
    ∀ p, p ∈ intrinsicBoundary B ↔ ‖(e p).val‖ = 1

lemma Family.hasPantsTopology (F : Family.{u,v}) (s : Waist) :
    HasPantsTopology (F.model s) := ⟨F.topology s,F.topological_boundary s⟩

structure PantsIsometry (B E : BorderedGeometry.{u,v}) where
  point : B.surface.Point ≃ᵢ E.surface.Point
  primitive : B.curves.Primitive ≃ E.curves.Primitive
  length : ∀ γ, E.curves.length (primitive γ) = B.curves.length γ
  trace : ∀ γ, E.curves.trace (primitive γ) = point '' B.curves.trace γ

/- Martelli Ch5 Prop1.6 pp84--87 gives uniqueness including two cusp cuffs.
The primitive equivalence, lengths and traces are the standard induced
transport of unoriented primitive geodesics under that actual isometry.
HasPantsTopology is essential: numeric genus/cusp fields alone are not used.
-/
structure UniquenessClassics (F : Family.{u,v}) : Prop where
  isometry : ∀ B : BorderedGeometry.{u,v}, HasPantsTopology B →
    ∀ R : BoundaryRealization B, B.boundaries = 1 → ∀ j : Fin B.boundaries,
    ∃ e : PantsIsometry B (F.model ⟨B.curves.length (R.curve j),
      (B.curves.representative (R.curve j)).period_pos⟩),
      e.primitive (R.curve j) =
        (F.boundary ⟨B.curves.length (R.curve j),
          (B.curves.representative (R.curve j)).period_pos⟩).curve
            (F.waist ⟨B.curves.length (R.curve j),
              (B.curves.representative (R.curve j)).period_pos⟩)

end WP.External.PantsCluster
