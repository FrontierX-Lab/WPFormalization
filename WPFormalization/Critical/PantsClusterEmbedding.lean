import WPFormalization.Critical.PantsClusterTransport

/-! Actual trace transport through intrinsic geodesic pieces.  A generic
intrinsic projection is deliberately not assumed injective: the two sides
of a nonseparating cut may have the same ambient boundary class.  The
disjointness statements below use the actual intrinsic interiors. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry Set

lemma curveParam_range (B : BorderedGeometry.{u,v}) (γ : B.curves.Primitive) :
    Set.range (curveParam B γ) = B.curves.trace γ := by
  ext p
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨_,⟨t,rfl⟩,rfl⟩
  · rintro ⟨_,⟨t,rfl⟩,rfl⟩
    exact ⟨t,rfl⟩

lemma primitive_trace_nonempty (B : BorderedGeometry.{u,v}) (γ : B.curves.Primitive) :
    (B.curves.trace γ).Nonempty :=
  ⟨curveParam B γ 0,⟨_,⟨0,rfl⟩,rfl⟩⟩

lemma intrinsicPiece_trace_projection {B : BorderedGeometry.{u,v}}
    (E : IntrinsicPiece B) (γ : E.model.curves.Primitive) :
    B.curves.trace (E.primitiveProjection γ) = E.point '' E.model.curves.trace γ := by
  obtain ⟨phase,reverse,hmap⟩ := E.axis_map γ
  let reparam : ℝ → ℝ := fun t => if reverse then phase-t else phase+t
  have hs : Function.Surjective reparam := by
    intro t
    cases reverse
    · refine ⟨t-phase,?_⟩
      simp only [reparam,Bool.false_eq_true,ite_false]
      ring
    · refine ⟨phase-t,?_⟩
      simp only [reparam,ite_true]
      ring
  rw [←curveParam_range,←curveParam_range]
  rw [←Set.range_comp]
  have he : E.point ∘ curveParam E.model γ =
      (curveParam B (E.primitiveProjection γ)) ∘ reparam := funext hmap
  rw [he,Set.range_comp,hs.range_eq,Set.image_univ]

lemma intrinsicPiece_trace_subset_interior_image {B : BorderedGeometry.{u,v}}
    (E : IntrinsicPiece B) (γ : E.model.curves.Primitive)
    (hγ : E.model.curves.trace γ ⊆ intrinsicInterior E.model) :
    B.curves.trace (E.primitiveProjection γ) ⊆ E.point '' intrinsicInterior E.model := by
  rw [intrinsicPiece_trace_projection]
  exact Set.image_mono hγ

lemma intrinsicPiece_projected_traces_disjoint {B : BorderedGeometry.{u,v}}
    (E F : IntrinsicPiece B)
    (hEF : Disjoint (E.point '' intrinsicInterior E.model)
      (F.point '' intrinsicInterior F.model))
    (γ : E.model.curves.Primitive) (δ : F.model.curves.Primitive)
    (hγ : E.model.curves.trace γ ⊆ intrinsicInterior E.model)
    (hδ : F.model.curves.trace δ ⊆ intrinsicInterior F.model) :
    Disjoint (B.curves.trace (E.primitiveProjection γ))
      (B.curves.trace (F.primitiveProjection δ)) :=
  hEF.mono (intrinsicPiece_trace_subset_interior_image E γ hγ)
    (intrinsicPiece_trace_subset_interior_image F δ hδ)

lemma intrinsicPiece_projected_primitives_ne {B : BorderedGeometry.{u,v}}
    (E F : IntrinsicPiece B)
    (hEF : Disjoint (E.point '' intrinsicInterior E.model)
      (F.point '' intrinsicInterior F.model))
    (γ : E.model.curves.Primitive) (δ : F.model.curves.Primitive)
    (hγ : E.model.curves.trace γ ⊆ intrinsicInterior E.model)
    (hδ : F.model.curves.trace δ ⊆ intrinsicInterior F.model) :
    E.primitiveProjection γ ≠ F.primitiveProjection δ := by
  intro he
  have hd := intrinsicPiece_projected_traces_disjoint E F hEF γ δ hγ hδ
  rw [he] at hd
  exact (primitive_trace_nonempty B _).ne_empty (disjoint_self.mp hd)

/-- A pure local consequence of actual trace uniqueness and interior
injectivity. The trace-uniqueness premise is geometric, not a pants or
ambient counting/classification hypothesis. -/
lemma intrinsicPiece_interior_projection_injective {B : BorderedGeometry.{u,v}}
    (E : IntrinsicPiece B) (htrace : Function.Injective E.model.curves.trace) :
    Function.Injective (fun γ : {γ : E.model.curves.Primitive //
      E.model.curves.trace γ ⊆ intrinsicInterior E.model} => E.primitiveProjection γ.val) := by
  intro γ δ hγδ
  change E.primitiveProjection γ.val = E.primitiveProjection δ.val at hγδ
  apply Subtype.ext
  apply htrace
  have he : E.point '' E.model.curves.trace γ.val = E.point '' E.model.curves.trace δ.val := by
    rw [←intrinsicPiece_trace_projection,←intrinsicPiece_trace_projection,hγδ]
  apply Set.Subset.antisymm
  · intro p hp
    have hm : E.point p ∈ E.point '' E.model.curves.trace δ.val := by
      rw [←he]
      exact ⟨p,hp,rfl⟩
    obtain ⟨q,hq,hqp⟩ := hm
    have hqp' : q=p := E.interior_injective (δ.property hq) (γ.property hp) hqp
    simpa only [hqp'] using hq
  · intro p hp
    have hm : E.point p ∈ E.point '' E.model.curves.trace γ.val := by
      rw [he]
      exact ⟨p,hp,rfl⟩
    obtain ⟨q,hq,hqp⟩ := hm
    have hqp' : q=p := E.interior_injective (γ.property hq) (δ.property hp) hqp
    simpa only [hqp'] using hq

end WP.Critical.PantsCluster
