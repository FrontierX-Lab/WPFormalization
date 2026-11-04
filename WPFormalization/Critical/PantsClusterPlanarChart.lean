import WPFormalization.Critical.PantsClusterPlanarLoop

/-! The actual open punctured-disk chart of the canonical pants interior.
Its open embedding, image and inverse identities are local topology proofs. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.ShortFillingGeometry Set

def openPantsDisk : Set ℂ :=
  {z | ‖z‖ < 1 ∧ z ≠ (1/2:ℂ) ∧ z ≠ -(1/2:ℂ)}

lemma openPantsDisk_isOpen : IsOpen openPantsDisk :=
  (isOpen_lt continuous_norm continuous_const).inter
    ((isOpen_ne : IsOpen {z : ℂ | z ≠ (1/2:ℂ)}).inter
      (isOpen_ne : IsOpen {z : ℂ | z ≠ -(1/2:ℂ)}))

def openPantsDiskToTwice : C(openPantsDisk,TwicePuncturedDisk) :=
  ⟨fun z => ⟨z.val,z.property.1.le,z.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩

lemma openPantsDiskToTwice_isOpenEmbedding :
    Topology.IsOpenEmbedding openPantsDiskToTwice := by
  let V : Set TwicePuncturedDisk := {z | ‖z.val‖ < 1}
  have hV : IsOpen V := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  let e : openPantsDisk ≃ₜ V := {
    toFun := fun z => ⟨⟨z.val,z.property.1.le,z.property.2⟩,z.property.1⟩
    invFun := fun z => ⟨z.val.val,z.property,z.val.property.2⟩
    left_inv := fun z => rfl
    right_inv := fun z => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hsub : Topology.IsOpenEmbedding (Subtype.val : V → TwicePuncturedDisk) :=
    ⟨.subtypeVal,by simpa using hV⟩
  exact hsub.comp e.isOpenEmbedding

def openPantsDiskToSurface (F : Family.{u,v}) (s : Waist) :
    C(openPantsDisk,(F.model s).surface.Point) :=
  ⟨fun z => (F.topology s).symm (openPantsDiskToTwice z),
    (F.topology s).symm.continuous.comp openPantsDiskToTwice.continuous⟩

lemma openPantsDiskToSurface_isOpenEmbedding (F : Family.{u,v}) (s : Waist) :
    Topology.IsOpenEmbedding (openPantsDiskToSurface F s) :=
  (F.topology s).symm.isOpenEmbedding.comp openPantsDiskToTwice_isOpenEmbedding

lemma pantsPlanarChart_openPantsDiskToSurface (F : Family.{u,v}) (s : Waist)
    (z : openPantsDisk) :
    pantsPlanarChart F s (openPantsDiskToSurface F s z) = z.val := by
  simp only [pantsPlanarChart,openPantsDiskToSurface,ContinuousMap.coe_mk,
    Homeomorph.apply_symm_apply]
  rfl

lemma openPantsDiskToSurface_range (F : Family.{u,v}) (s : Waist) :
    Set.range (openPantsDiskToSurface F s) = intrinsicInterior (F.model s) := by
  ext p
  constructor
  · rintro ⟨z,rfl⟩
    apply (canonical_pants_interior_iff F s _).mpr
    change ‖pantsPlanarChart F s (openPantsDiskToSurface F s z)‖ < 1
    rw [pantsPlanarChart_openPantsDiskToSurface]
    exact z.property.1
  · intro hp
    let z : openPantsDisk := ⟨pantsPlanarChart F s p,
      (canonical_pants_interior_iff F s p).mp hp,((F.topology s p).property).2⟩
    refine ⟨z,?_⟩
    apply pantsPlanarChart_injective F s
    exact pantsPlanarChart_openPantsDiskToSurface F s z

end WP.Critical.PantsCluster
