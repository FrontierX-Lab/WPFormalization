import WPFormalization.Critical.PantsClusterCutEmbedding
import WPFormalization.Critical.PantsClusterGenericSimple
import WPFormalization.Critical.ShortConfigurationIntrinsicSimpleLift

/-! Distinct actual cut components have disjoint complete projected primitive
catalogs when their formal boundary sides use distinct actual cut edges.
No filling, short-curve existence, or spectrum partition is assumed here. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry Set
open WP.External.PantsCluster WP.External.ShortBorderedLoopGeometry
open WP.External.PlanarJordanGeometry WP.External.PlanarRegionGeometry
open WP.External.ShortBorderedPeripheralGeometry

/-- Actual ambient simplicity lifts intrinsically, so on an actual pants
only its actual boundary primitive can have a simple ambient projection. -/
lemma intrinsic_pants_projection_simple_iff_boundary {B : BorderedGeometry.{u,v}}
    (E : IntrinsicPiece B) (hp : HasPantsTopology E.model)
    (hb : E.model.boundaries = 1)
    (BC : PrimitiveBoundaryClassics E.model E.boundary)
    (LS : BorderedLoopStraighteningClassics E.model E.boundary)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics E.model E.boundary)
    (β : E.model.curves.Primitive) (j : Fin E.model.boundaries) :
    SimpleTrace B (E.primitiveProjection β) ↔ β = E.boundary.curve j := by
  constructor
  · intro hs
    exact (actual_pants_simple_iff_boundary E.model hp E.boundary hb BC LS J PC PP β j).mp
      (WP.Critical.ShortConfiguration.intrinsicPiece_simple_of_projection_simple E β hs)
  · rintro rfl
    exact E.boundary_simple j

lemma intrinsic_pants_simple_mem_projected_range_iff {B : BorderedGeometry.{u,v}}
    (E : IntrinsicPiece B) (hp : HasPantsTopology E.model)
    (hb : E.model.boundaries = 1)
    (BC : PrimitiveBoundaryClassics E.model E.boundary)
    (LS : BorderedLoopStraighteningClassics E.model E.boundary)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics E.model E.boundary)
    (j : Fin E.model.boundaries) (γ : B.curves.Primitive) (hs : SimpleTrace B γ) :
    γ ∈ Set.range E.primitiveProjection ↔ γ = E.primitiveProjection (E.boundary.curve j) := by
  constructor
  · rintro ⟨β,rfl⟩
    rw [(intrinsic_pants_projection_simple_iff_boundary E hp hb BC LS J PC PP β j).mp hs]
  · rintro rfl
    exact ⟨E.boundary.curve j,rfl⟩

variable {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G} (A : AmbientRealization H)
  {T : MulticurveTopology.{u,v,w,z} G H} {g n k : ℕ} {o : T.Orbit g n k}
  {X : G.Moduli g n (fun _ => 0)} {κ : Fin k → H.Primitive g n X}
  {hκ : T.orbitMem o X κ} (C : CutComponentRealization A T o X κ hκ)

lemma cutComponent_boundary_projection_ne_of_edge_ne
    (c d : Fin (T.cut o).components)
    (i : Fin (C.piece c).model.boundaries) (j : Fin (C.piece d).model.boundaries)
    (hij : (C.halfSideEquiv c i).val.1 ≠ (C.halfSideEquiv d j).val.1) :
    (C.piece c).primitiveProjection ((C.piece c).boundary.curve i) ≠
      (C.piece d).primitiveProjection ((C.piece d).boundary.curve j) := by
  rw [C.boundary_eq c i,C.boundary_eq d j]
  intro h
  exact hij ((T.orbit_injective o X κ hκ) ((A.primitiveEquiv g n X).injective h))

lemma cutComponent_projected_ranges_disjoint
    (c d : Fin (T.cut o).components) (hcd : c ≠ d)
    (hc : ∀ γ : (C.piece c).model.curves.Primitive,
      (C.piece c).model.curves.trace γ ⊆ intrinsicInterior (C.piece c).model ∨
        ∃ j, (C.piece c).boundary.curve j = γ)
    (hd : ∀ γ : (C.piece d).model.curves.Primitive,
      (C.piece d).model.curves.trace γ ⊆ intrinsicInterior (C.piece d).model ∨
        ∃ j, (C.piece d).boundary.curve j = γ)
    (hedge : ∀ i : Fin (C.piece c).model.boundaries,
      ∀ j : Fin (C.piece d).model.boundaries,
      (C.halfSideEquiv c i).val.1 ≠ (C.halfSideEquiv d j).val.1) :
    Disjoint (Set.range (C.piece c).primitiveProjection)
      (Set.range (C.piece d).primitiveProjection) := by
  apply Set.disjoint_left.mpr
  rintro γ ⟨β,rfl⟩ ⟨δ,he⟩
  rcases hc β with hβ | ⟨i,rfl⟩
  · rcases hd δ with hδ | ⟨j,rfl⟩
    · exact intrinsicPiece_projected_primitives_ne (C.piece c) (C.piece d)
        (cutComponent_interior_images_disjoint A C c d hcd) β δ hβ hδ he.symm
    · rw [C.boundary_eq d j] at he
      exact cutComponent_interior_primitive_ne_cut A C c β hβ _ he.symm
  · rcases hd δ with hδ | ⟨j,rfl⟩
    · rw [C.boundary_eq c i] at he
      exact cutComponent_interior_primitive_ne_cut A C d δ hδ _ he
    · exact cutComponent_boundary_projection_ne_of_edge_ne A C c d i j (hedge i j) he.symm

end WP.Critical.PantsCluster
