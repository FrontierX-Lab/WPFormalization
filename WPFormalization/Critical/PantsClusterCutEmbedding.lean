import WPFormalization.Critical.PantsClusterEmbedding

/-! True intrinsic components of the actual multicurve cut. Their interior
primitive images avoid every cut curve. No filling classification or assumed
primitive-catalog partition is used. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry Set

variable {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G} (A : AmbientRealization H)
  {T : MulticurveTopology.{u,v,w,z} G H} {g n k : ℕ} {o : T.Orbit g n k}
  {X : G.Moduli g n (fun _ => 0)} {κ : Fin k → H.Primitive g n X}
  {hκ : T.orbitMem o X κ} (C : CutComponentRealization A T o X κ hκ)

lemma cutComponent_interior_subset_cutComplement (c : Fin (T.cut o).components) :
    (C.piece c).point '' intrinsicInterior (C.piece c).model ⊆ cutComplement A κ := by
  rw [C.image_eq c]
  rintro p ⟨hp,_⟩
  exact hp

lemma cutComplement_disjoint_cut_trace (i : Fin k) :
    Disjoint (cutComplement A κ)
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ i))) := by
  apply Set.disjoint_left.mpr
  intro p hp hpi
  exact hp i hpi

lemma cutComponent_interior_trace_disjoint_cut (c : Fin (T.cut o).components)
    (γ : (C.piece c).model.curves.Primitive)
    (hγ : (C.piece c).model.curves.trace γ ⊆ intrinsicInterior (C.piece c).model)
    (i : Fin k) :
    Disjoint ((A.model g n X).curves.trace ((C.piece c).primitiveProjection γ))
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ i))) := by
  exact (cutComplement_disjoint_cut_trace A i).mono_left
    ((intrinsicPiece_trace_subset_interior_image (C.piece c) γ hγ).trans
      (cutComponent_interior_subset_cutComplement A C c))

lemma cutComponent_interior_primitive_ne_cut (c : Fin (T.cut o).components)
    (γ : (C.piece c).model.curves.Primitive)
    (hγ : (C.piece c).model.curves.trace γ ⊆ intrinsicInterior (C.piece c).model)
    (i : Fin k) :
    (C.piece c).primitiveProjection γ ≠ A.primitiveEquiv g n X (κ i) := by
  intro he
  have hd := cutComponent_interior_trace_disjoint_cut A C c γ hγ i
  rw [he] at hd
  exact (primitive_trace_nonempty _ _).ne_empty (disjoint_self.mp hd)

lemma cutComponent_interior_primitive_ne_boundary (c : Fin (T.cut o).components)
    (γ : (C.piece c).model.curves.Primitive)
    (hγ : (C.piece c).model.curves.trace γ ⊆ intrinsicInterior (C.piece c).model)
    (j : Fin (C.piece c).model.boundaries) :
    (C.piece c).primitiveProjection γ ≠
      (C.piece c).primitiveProjection ((C.piece c).boundary.curve j) := by
  rw [C.boundary_eq c j]
  exact cutComponent_interior_primitive_ne_cut A C c γ hγ _

lemma cutComponent_interior_images_disjoint (c d : Fin (T.cut o).components) (hcd : c ≠ d) :
    Disjoint ((C.piece c).point '' intrinsicInterior (C.piece c).model)
      ((C.piece d).point '' intrinsicInterior (C.piece d).model) := by
  rw [C.image_eq c,C.image_eq d]
  apply Set.disjoint_left.mpr
  rintro p ⟨hp,hpc⟩ ⟨hq,hpd⟩
  exact hcd (hpc.symm.trans hpd)

lemma cutComponent_interior_sigma_projection_injective
    (htrace : ∀ c : Fin (T.cut o).components,
      Function.Injective (C.piece c).model.curves.trace) :
    Function.Injective (fun γ : (Σ c : Fin (T.cut o).components,
      {γ : (C.piece c).model.curves.Primitive //
        (C.piece c).model.curves.trace γ ⊆ intrinsicInterior (C.piece c).model}) =>
      (C.piece γ.1).primitiveProjection γ.2.val) := by
  rintro ⟨c,γ⟩ ⟨d,δ⟩ h
  have hcd : c=d := by
    by_contra hcd
    exact (intrinsicPiece_projected_primitives_ne (C.piece c) (C.piece d)
      (cutComponent_interior_images_disjoint A C c d hcd)
      γ.val δ.val γ.property δ.property) h
  subst d
  congr 1
  exact intrinsicPiece_interior_projection_injective (C.piece c) (htrace c) h

/-- Unlike a general intrinsic cut piece, a one-boundary component has no
pair of formal boundary copies that could project to the same ambient curve.
The only geometric premises are trace uniqueness and the generic
interior/boundary dichotomy, not a pants spectrum or count assertion. -/
lemma cutComponent_single_boundary_projection_injective (c : Fin (T.cut o).components)
    (hb : (C.piece c).model.boundaries = 1)
    (htrace : Function.Injective (C.piece c).model.curves.trace)
    (hside : ∀ γ : (C.piece c).model.curves.Primitive,
      (C.piece c).model.curves.trace γ ⊆ intrinsicInterior (C.piece c).model ∨
        ∃ j, (C.piece c).boundary.curve j = γ) :
    Function.Injective (C.piece c).primitiveProjection := by
  intro γ δ h
  rcases hside γ with hγ|⟨j,rfl⟩
  · rcases hside δ with hδ|⟨j,rfl⟩
    · exact congrArg Subtype.val
        (intrinsicPiece_interior_projection_injective (C.piece c) htrace
          (show (C.piece c).primitiveProjection (⟨γ,hγ⟩ : {β //
            (C.piece c).model.curves.trace β ⊆ intrinsicInterior (C.piece c).model}).val =
              (C.piece c).primitiveProjection (⟨δ,hδ⟩ : {β //
            (C.piece c).model.curves.trace β ⊆ intrinsicInterior (C.piece c).model}).val from h))
    · exact (cutComponent_interior_primitive_ne_boundary A C c γ hγ j h).elim
  · rcases hside δ with hδ|⟨i,rfl⟩
    · exact (cutComponent_interior_primitive_ne_boundary A C c δ hδ j h.symm).elim
    · have hij : i=j := by
        apply Fin.ext
        have hi := i.isLt
        have hj := j.isLt
        omega
      rw [hij]

end WP.Critical.PantsCluster
