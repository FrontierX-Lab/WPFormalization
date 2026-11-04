import WPFormalization.Critical.PantsClusterTwoPunctures

/-! The actual-topology proof works for every bordered pants, independently of
any Fenchel--Nielsen family or isometric-transport assumption. Chart is only a
bundle of actual data supplied by HasPantsTopology and BoundaryRealization. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster.GenericPants
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry Set
open WP.External.PlanarJordanGeometry WP.External.PlanarRegionGeometry
open WP.External.ShortBorderedPeripheralGeometry

structure Chart where
  model : BorderedGeometry.{u,v}
  topology : model.surface.Point ≃ₜ TwicePuncturedDisk
  topological_boundary : ∀ p, p ∈ intrinsicBoundary model ↔ ‖(topology p).val‖ = 1
  boundary : BoundaryRealization model
  boundaries : model.boundaries = 1
  waist : Fin model.boundaries

lemma canonical_pants_interior_iff (C : Chart.{u,v}) (p : C.model.surface.Point) :
    p ∈ intrinsicInterior C.model ↔ ‖(C.topology p).val‖ < 1 := by
  rw [intrinsic_interior_eq_compl_boundary,Set.mem_compl_iff,C.topological_boundary]
  have hle := (C.topology p).property.1
  exact ⟨fun h => lt_of_le_of_ne hle h,ne_of_lt⟩

lemma canonical_boundary_index_eq (C : Chart.{u,v}) (j : Fin C.model.boundaries) :
    j = C.waist := by
  apply Fin.ext
  have hj := j.isLt
  have hw := C.waist.isLt
  have hb := C.boundaries
  omega

lemma canonical_nonwaist_trace_interior (C : Chart.{u,v})
    (BC : PrimitiveBoundaryClassics C.model C.boundary)
    (γ : C.model.curves.Primitive) (hγ : γ ≠ C.boundary.curve C.waist) :
    C.model.curves.trace γ ⊆ intrinsicInterior C.model := by
  rcases BC.interior_or_boundary γ with hi|⟨j,hj⟩
  · exact hi
  · rw [canonical_boundary_index_eq C j] at hj
    exact (hγ hj.symm).elim

lemma canonical_waist_simple (C : Chart.{u,v}) :
    SimpleTrace C.model (C.boundary.curve C.waist) := C.boundary.simple C.waist

lemma canonical_waist_trace_eq_boundary (C : Chart.{u,v}) :
    C.model.curves.trace (C.boundary.curve C.waist) = intrinsicBoundary C.model := by
  rw [←C.boundary.cover]
  ext p
  simp only [Set.mem_iUnion]
  exact ⟨fun hp => ⟨C.waist,hp⟩,fun ⟨j,hj⟩ =>
    (canonical_boundary_index_eq C j) ▸ hj⟩

def pantsPlanarChart (C : Chart.{u,v}) : C(C.model.surface.Point,ℂ) :=
  ⟨fun p => (C.topology p).val,
    continuous_subtype_val.comp C.topology.continuous⟩

lemma pantsPlanarChart_injective (C : Chart.{u,v}) :
    Function.Injective (pantsPlanarChart C) :=
  Subtype.val_injective.comp C.topology.injective

def planarPrimitiveLoop (C : Chart.{u,v}) (γ : C.model.curves.Primitive) : ClosedLoop ℂ :=
  mapClosedLoop (pantsPlanarChart C) (primitiveLoop C.model (γ))

lemma planarPrimitiveLoop_trace (C : Chart.{u,v}) (γ : C.model.curves.Primitive) :
    (planarPrimitiveLoop C γ).trace =
      pantsPlanarChart C '' C.model.curves.trace (γ) := by
  rw [planarPrimitiveLoop,mapClosedLoop_trace,
    WP.Critical.ShortConfiguration.primitiveLoop_trace]

lemma planarPrimitiveLoop_simple (C : Chart.{u,v}) (γ : C.model.curves.Primitive)
    (hγ : SimpleTrace C.model (γ)) :
    (planarPrimitiveLoop C γ).Simple :=
  mapClosedLoop_simple (pantsPlanarChart C) (pantsPlanarChart_injective C) _
    (WP.Critical.ShortConfiguration.primitiveLoop_simple _ _ hγ)

lemma planarPrimitiveLoop_avoids_punctures (C : Chart.{u,v})
    (γ : C.model.curves.Primitive) :
    ∀ z ∈ (planarPrimitiveLoop C γ).trace, z ≠ (1/2:ℂ) ∧ z ≠ -(1/2:ℂ) := by
  rw [planarPrimitiveLoop_trace]
  rintro _ ⟨p,hp,rfl⟩
  exact ((C.topology p).property).2

lemma planarPrimitiveLoop_nonwaist_inside_unitDisk (C : Chart.{u,v})
    (BC : PrimitiveBoundaryClassics C.model C.boundary)
    (γ : C.model.curves.Primitive) (hγ : γ ≠ (C.boundary.curve C.waist)) :
    ∀ z ∈ (planarPrimitiveLoop C γ).trace, ‖z‖ < 1 := by
  rw [planarPrimitiveLoop_trace]
  rintro _ ⟨p,hp,rfl⟩
  exact (canonical_pants_interior_iff C p).mp
    (canonical_nonwaist_trace_interior C BC γ hγ hp)

lemma planarPrimitiveLoop_has_boundedDisk (C : Chart.{u,v})
    (J : PlanarJordanClassics) (γ : C.model.curves.Primitive)
    (hγ : SimpleTrace C.model (γ)) :
    Nonempty (DiskBoundedBy (planarPrimitiveLoop C γ)) :=
  simple_plane_loop_boundedDisk J _ (planarPrimitiveLoop_simple C γ hγ)

lemma planarPrimitiveLoop_boundedDisk_inside_unitDisk (C : Chart.{u,v})
    (BC : PrimitiveBoundaryClassics C.model C.boundary)
    (γ : C.model.curves.Primitive) (hγ : γ ≠ (C.boundary.curve C.waist))
    (D : DiskBoundedBy (planarPrimitiveLoop C γ)) :
    ∀ z ∈ Set.range D.map, ‖z‖ < 1 :=
  boundedDisk_subset_open_unitDisk D
    (planarPrimitiveLoop_nonwaist_inside_unitDisk C BC γ hγ)


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

def openPantsDiskToSurface (C : Chart.{u,v}) :
    C(openPantsDisk,C.model.surface.Point) :=
  ⟨fun z => C.topology.symm (openPantsDiskToTwice z),
    C.topology.symm.continuous.comp openPantsDiskToTwice.continuous⟩

lemma openPantsDiskToSurface_isOpenEmbedding (C : Chart.{u,v}) :
    Topology.IsOpenEmbedding (openPantsDiskToSurface C) :=
  C.topology.symm.isOpenEmbedding.comp openPantsDiskToTwice_isOpenEmbedding

lemma pantsPlanarChart_openPantsDiskToSurface (C : Chart.{u,v})
    (z : openPantsDisk) :
    pantsPlanarChart C (openPantsDiskToSurface C z) = z.val := by
  simp only [pantsPlanarChart,openPantsDiskToSurface,ContinuousMap.coe_mk,
    Homeomorph.apply_symm_apply]
  rfl

lemma openPantsDiskToSurface_range (C : Chart.{u,v}) :
    Set.range (openPantsDiskToSurface C) = intrinsicInterior C.model := by
  ext p
  constructor
  · rintro ⟨z,rfl⟩
    apply (canonical_pants_interior_iff C _).mpr
    change ‖pantsPlanarChart C (openPantsDiskToSurface C z)‖ < 1
    rw [pantsPlanarChart_openPantsDiskToSurface]
    exact z.property.1
  · intro hp
    let z : openPantsDisk := ⟨pantsPlanarChart C p,
      (canonical_pants_interior_iff C p).mp hp,((C.topology p).property).2⟩
    refine ⟨z,?_⟩
    apply pantsPlanarChart_injective C
    exact pantsPlanarChart_openPantsDiskToSurface C z


lemma canonical_nonwaist_JordanDisk_contains_puncture (C : Chart.{u,v})
    (BC : PrimitiveBoundaryClassics C.model C.boundary)
    (LS : BorderedLoopStraighteningClassics C.model C.boundary)
    (γ : C.model.curves.Primitive) (hγ : γ ≠ (C.boundary.curve C.waist))
    (D : DiskBoundedBy (planarPrimitiveLoop C γ)) :
    (1/2:ℂ) ∈ Set.range D.map ∨ -(1/2:ℂ) ∈ Set.range D.map := by
  by_contra hn
  rcases not_or.mp hn with ⟨hp,hm⟩
  have hf : ∀ t, (planarPrimitiveLoop C γ).map t ∈ openPantsDisk := by
    intro t
    exact ⟨planarPrimitiveLoop_nonwaist_inside_unitDisk C BC γ hγ _ ⟨t,rfl⟩,
      planarPrimitiveLoop_avoids_punctures C γ _ ⟨t,rfl⟩⟩
  have hD : ∀ z, D.map z ∈ openPantsDisk := by
    intro z
    refine ⟨planarPrimitiveLoop_boundedDisk_inside_unitDisk C BC γ hγ D _ ⟨z,rfl⟩,?_,?_⟩
    · intro hz
      exact hp ⟨z,hz⟩
    · intro hz
      exact hm ⟨z,hz⟩
  let E := boundedDisk_liftOpen openPantsDisk openPantsDisk_isOpen D hf hD
  let R := boundedDisk_mapOpenEmbedding (openPantsDiskToSurface C)
    (openPantsDiskToSurface_isOpenEmbedding C) E
  have he : mapClosedLoop (openPantsDiskToSurface C)
      (subtypeClosedLoop openPantsDisk (planarPrimitiveLoop C γ) hf) =
        primitiveLoop C.model (γ) := by
    apply WP.Critical.ShortConfiguration.ClosedLoop.ext_map
    ext t
    apply pantsPlanarChart_injective C
    change pantsPlanarChart C (openPantsDiskToSurface C _) =
      pantsPlanarChart C ((primitiveLoop C.model (γ)).map t)
    rw [pantsPlanarChart_openPantsDiskToSurface]
    rfl
  have hR : DiskBoundedBy (primitiveLoop C.model (γ)) := he ▸ R
  exact WP.Critical.ShortConfiguration.ClosedLoop.not_positive_of_nullhomotopic _
    (WP.Critical.ShortConfiguration.disk_loop_nullhomotopic hR _ (boundedDisk_trace_subset hR))
    (bordered_primitive_positiveHomotopyLength C.model C.boundary LS (γ))


lemma canonical_puncture_mem_disk_interior (C : Chart.{u,v})
    (γ : C.model.curves.Primitive) (D : DiskBoundedBy (planarPrimitiveLoop C γ))
    {p : ℂ} (hp : p = (1/2:ℂ) ∨ p = -(1/2:ℂ))
    (hD : p ∈ Set.range D.map) : p ∈ interior (Set.range D.map) := by
  apply boundedDisk_mem_interior_of_mem_not_trace D hD
  intro hf
  rcases planarPrimitiveLoop_avoids_punctures C γ p hf with ⟨hplus,hminus⟩
  exact hp.elim hplus hminus

lemma canonical_nonwaist_JordanDisk_contains_interior_puncture (C : Chart.{u,v}) (BC : PrimitiveBoundaryClassics C.model C.boundary)
    (LS : BorderedLoopStraighteningClassics C.model C.boundary)
    (γ : C.model.curves.Primitive) (hγ : γ ≠ (C.boundary.curve C.waist))
    (D : DiskBoundedBy (planarPrimitiveLoop C γ)) :
    (1/2:ℂ) ∈ interior (Set.range D.map) ∨
      -(1/2:ℂ) ∈ interior (Set.range D.map) := by
  rcases canonical_nonwaist_JordanDisk_contains_puncture C BC LS γ hγ D with h | h
  · exact Or.inl (canonical_puncture_mem_disk_interior C γ D (Or.inl rfl) h)
  · exact Or.inr (canonical_puncture_mem_disk_interior C γ D (Or.inr rfl) h)


lemma pants_chart_disk_region_frontier (C : Chart.{u,v})
    (γ : C.model.curves.Primitive) (D : DiskBoundedBy (planarPrimitiveLoop C γ))
    (hD : ∀ z ∈ Set.range D.map, ‖z‖ < 1) :
    frontier (pantsPlanarChart C ⁻¹' Set.range D.map) =
      C.model.curves.trace (γ) := by
  let A : Set openPantsDisk := Subtype.val ⁻¹' Set.range D.map
  let h := openPantsDiskToSurface C
  have hi : ∀ p, p ∈ pantsPlanarChart C ⁻¹' Set.range D.map →
      p ∈ intrinsicInterior C.model := by
    intro p hp
    exact (canonical_pants_interior_iff C p).mpr (hD _ hp)
  have hrange : h '' A = pantsPlanarChart C ⁻¹' Set.range D.map := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      change pantsPlanarChart C (openPantsDiskToSurface C z) ∈ Set.range D.map
      rwa [pantsPlanarChart_openPantsDiskToSurface]
    · intro hp
      have := hi p hp
      rw [←openPantsDiskToSurface_range] at this
      obtain ⟨z,rfl⟩ := this
      refine ⟨z,?_,rfl⟩
      change z.val ∈ Set.range D.map
      rw [←pantsPlanarChart_openPantsDiskToSurface C z]
      exact hp
  have hclosed : IsClosed (h '' A) := by
    rw [hrange]
    exact (boundedDisk_range_isCompact D).isClosed.preimage (pantsPlanarChart C).continuous
  rw [←hrange,openEmbedding_image_frontier_of_closed_image
    (openPantsDiskToSurface_isOpenEmbedding C) A hclosed]
  have hfront : frontier A = Subtype.val ⁻¹' (planarPrimitiveLoop C γ).trace := by
    change frontier (Subtype.val ⁻¹' Set.range D.map) = _
    rw [←openPantsDisk_isOpen.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val,D.frontier_eq]
  rw [hfront]
  ext p
  constructor
  · rintro ⟨z,hz,rfl⟩
    rw [planarPrimitiveLoop_trace] at hz
    obtain ⟨q,hq,heq⟩ := hz
    have hh : openPantsDiskToSurface C z = q := by
      apply pantsPlanarChart_injective C
      rw [pantsPlanarChart_openPantsDiskToSurface]
      exact heq.symm
    simpa only [h,hh] using hq
  · intro hp
    have hz : pantsPlanarChart C p ∈ Set.range D.map :=
      boundedDisk_trace_subset D (by rw [planarPrimitiveLoop_trace];exact ⟨p,hp,rfl⟩)
    let z : openPantsDisk := ⟨pantsPlanarChart C p,hD _ hz,
      ((C.topology p).property).2⟩
    refine ⟨z,?_,?_⟩
    · change z.val ∈ (planarPrimitiveLoop C γ).trace
      rw [planarPrimitiveLoop_trace]
      exact ⟨p,hp,rfl⟩
    · apply pantsPlanarChart_injective C
      exact pantsPlanarChart_openPantsDiskToSurface C z

def puncturedDisk_pantsRegionHomeomorph (C : Chart.{u,v})
    {f : ClosedLoop ℂ} (D : DiskBoundedBy f) (p : ℂ)
    (hp : p = (1/2:ℂ) ∨ p = -(1/2:ℂ))
    (hD : ∀ z ∈ Set.range D.map, ‖z‖ < 1)
    (hother : ∀ z ∈ Set.range D.map, z ≠ p → z ≠ (1/2:ℂ) ∧ z ≠ -(1/2:ℂ)) :
    {z : ℂ // z ∈ Set.range D.map ∧ z ≠ p} ≃ₜ
      {x : C.model.surface.Point // pantsPlanarChart C x ∈ Set.range D.map} where
  toFun z := ⟨C.topology.symm
    ⟨z.val,(hD z.val z.property.1).le,hother _ z.property.1 z.property.2⟩,by
      change pantsPlanarChart C (C.topology.symm _) ∈ _
      simpa only [pantsPlanarChart,ContinuousMap.coe_mk,Homeomorph.apply_symm_apply]
        using z.property.1⟩
  invFun x := ⟨pantsPlanarChart C x.val,x.property,by
    rcases hp with rfl|rfl
    · exact ((C.topology x.val).property).2.1
    · exact ((C.topology x.val).property).2.2⟩
  left_inv z := by apply Subtype.ext; simp [pantsPlanarChart]
  right_inv x := by apply Subtype.ext; exact C.topology.symm_apply_apply x.val
  continuous_toFun := by fun_prop
  continuous_invFun := by
    exact ((pantsPlanarChart C).continuous.comp continuous_subtype_val).subtype_mk _

lemma puncturedDisk_pantsRegionHomeomorph_apply_chart (C : Chart.{u,v})
    {f : ClosedLoop ℂ} (D : DiskBoundedBy f) (p : ℂ)
    (hp : p = (1/2:ℂ) ∨ p = -(1/2:ℂ))
    (hD : ∀ z ∈ Set.range D.map, ‖z‖ < 1)
    (hother : ∀ z ∈ Set.range D.map, z ≠ p → z ≠ (1/2:ℂ) ∧ z ≠ -(1/2:ℂ))
    (z : {z : ℂ // z ∈ Set.range D.map ∧ z ≠ p}) :
    pantsPlanarChart C ((puncturedDisk_pantsRegionHomeomorph C D p hp hD hother z).val) =
      z.val := by
  change (C.topology (C.topology.symm _)).val = z.val
  rw [Homeomorph.apply_symm_apply]


def canonicalPuncturedDiskCuspEnd (C : Chart.{u,v})
    (γ : C.model.curves.Primitive) (D : DiskBoundedBy (planarPrimitiveLoop C γ)) (p : ℂ)
    (hp : p = (1/2:ℂ) ∨ p = -(1/2:ℂ))
    (hD : ∀ z ∈ Set.range D.map, ‖z‖ < 1)
    (hother : ∀ z ∈ Set.range D.map, z ≠ p → z ≠ (1/2:ℂ) ∧ z ≠ -(1/2:ℂ))
    (K : PuncturedDiskCoordinates D p) :
    CuspEndBoundedBy (primitiveLoop C.model (γ)) := by
  let e := K.coordinates.trans (puncturedDisk_pantsRegionHomeomorph C D p hp hD hother)
  let map : C(LoopCircle × Ici (0:ℝ),C.model.surface.Point) :=
    ⟨fun z => (e z).val,continuous_subtype_val.comp e.continuous⟩
  have hmap (w : LoopCircle × Ici (0:ℝ)) :
      pantsPlanarChart C (map w) = (K.coordinates w).val := by
    exact puncturedDisk_pantsRegionHomeomorph_apply_chart C D p hp hD hother (K.coordinates w)
  have hrange : Set.range map = pantsPlanarChart C ⁻¹' Set.range D.map := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩
      exact (e w).property
    · intro hz
      exact ⟨e.symm ⟨z,hz⟩,by simp only [map,ContinuousMap.coe_mk,e.apply_symm_apply]⟩
  have hinner : map '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val} =
      pantsPlanarChart C ⁻¹' interior (Set.range D.map) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      have hK := show K.coordinates w ∈
          K.coordinates '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val} from ⟨w,hw,rfl⟩
      rw [K.inner_range] at hK
      change pantsPlanarChart C (map w) ∈ interior (Set.range D.map)
      rw [hmap]
      exact hK
    · intro hz
      have hDz : pantsPlanarChart C z ∈ Set.range D.map := interior_subset hz
      have hneq : pantsPlanarChart C z ≠ p := by
        rcases hp with rfl|rfl
        · exact ((C.topology z).property).2.1
        · exact ((C.topology z).property).2.2
      have hK : (⟨pantsPlanarChart C z,hDz,hneq⟩ :
          {z : ℂ // z ∈ Set.range D.map ∧ z ≠ p}) ∈
          K.coordinates '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val} := by
        rw [K.inner_range]
        exact hz
      obtain ⟨w,hw,hew⟩ := hK
      refine ⟨w,hw,?_⟩
      apply pantsPlanarChart_injective C
      rw [hmap]
      exact congrArg (fun v : {z : ℂ // z ∈ Set.range D.map ∧ z ≠ p} => v.val) hew
  refine {
    map := map
    closedEmbedding := ⟨?_,?_⟩
    boundary := ?_
    inner_open := ?_
    frontier_eq := ?_ }
  · exact Topology.IsEmbedding.subtypeVal.comp e.isEmbedding
  · rw [hrange]
    exact (boundedDisk_range_isCompact D).isClosed.preimage (pantsPlanarChart C).continuous
  · intro z
    apply pantsPlanarChart_injective C
    rw [hmap,K.boundary]
    exact mapClosedLoop_circleMap (pantsPlanarChart C) _ z
  · rw [hinner]
    exact isOpen_interior.preimage (pantsPlanarChart C).continuous
  · rw [hrange,pants_chart_disk_region_frontier C γ D hD,
      WP.Critical.ShortConfiguration.primitiveLoop_trace]

lemma canonical_JordanDisk_not_one_puncture (C : Chart.{u,v})
    (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics C.model C.boundary)
    (γ : C.model.curves.Primitive) (D : DiskBoundedBy (planarPrimitiveLoop C γ)) (p : ℂ)
    (hp : p = (1/2:ℂ) ∨ p = -(1/2:ℂ)) (hpD : p ∈ Set.range D.map)
    (hD : ∀ z ∈ Set.range D.map, ‖z‖ < 1)
    (hother : ∀ z ∈ Set.range D.map, z ≠ p → z ≠ (1/2:ℂ) ∧ z ≠ -(1/2:ℂ)) : False := by
  obtain ⟨K⟩ := PC.punctured_disk D p (canonical_puncture_mem_disk_interior C γ D hp hpD)
  let E := canonicalPuncturedDiskCuspEnd C γ D p hp hD hother K
  apply PP.cusp_no_axial _ E (γ)
  rw [←WP.Critical.ShortConfiguration.primitiveLoop_trace]
  exact cuspEnd_trace_subset E

lemma canonical_nonwaist_JordanDisk_contains_both_punctures (C : Chart.{u,v}) (BC : PrimitiveBoundaryClassics C.model C.boundary)
    (LS : BorderedLoopStraighteningClassics C.model C.boundary)
    (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics C.model C.boundary)
    (γ : C.model.curves.Primitive) (hγ : γ ≠ (C.boundary.curve C.waist))
    (D : DiskBoundedBy (planarPrimitiveLoop C γ)) :
    (1/2:ℂ) ∈ interior (Set.range D.map) ∧
      -(1/2:ℂ) ∈ interior (Set.range D.map) := by
  have hD := planarPrimitiveLoop_boundedDisk_inside_unitDisk C BC γ hγ D
  have he := canonical_nonwaist_JordanDisk_contains_puncture C BC LS γ hγ D
  have hboth : (1/2:ℂ) ∈ Set.range D.map ∧ -(1/2:ℂ) ∈ Set.range D.map := by
    rcases he with hp|hm
    · refine ⟨hp,?_⟩
      by_contra hn
      apply canonical_JordanDisk_not_one_puncture C PC PP γ D (1/2:ℂ) (Or.inl rfl) hp hD
      intro z hz hzp
      exact ⟨hzp,fun hzm => hn (hzm ▸ hz)⟩
    · refine ⟨?_,hm⟩
      by_contra hn
      apply canonical_JordanDisk_not_one_puncture C PC PP γ D (-(1/2:ℂ)) (Or.inr rfl) hm hD
      intro z hz hzm
      exact ⟨fun hzp => hn (hzp ▸ hz),hzm⟩
  exact ⟨canonical_puncture_mem_disk_interior C γ D (Or.inl rfl) hboth.1,
    canonical_puncture_mem_disk_interior C γ D (Or.inr rfl) hboth.2⟩


lemma canonical_waist_planar_trace (C : Chart.{u,v}) :
    (planarPrimitiveLoop C (C.boundary.curve C.waist)).trace = Metric.sphere (0:ℂ) 1 := by
  rw [planarPrimitiveLoop_trace,canonical_waist_trace_eq_boundary]
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    simpa only [Metric.mem_sphere,dist_zero_right,pantsPlanarChart,ContinuousMap.coe_mk] using (C.topological_boundary p).mp hp
  · intro hz
    have hn : ‖z‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hz
    have hp : z ≠ (1/2:ℂ) := by intro h;rw [h] at hn;norm_num at hn
    have hm : z ≠ -(1/2:ℂ) := by intro h;rw [h] at hn;norm_num at hn
    let p := C.topology.symm ⟨z,hn.le,hp,hm⟩
    refine ⟨p,?_,?_⟩
    · apply (C.topological_boundary p).mpr
      simp only [p,Homeomorph.apply_symm_apply]
      exact hn
    · change (C.topology (C.topology.symm _)).val = z
      simp only [Homeomorph.apply_symm_apply]



def waistCircleHomeomorph (C : Chart.{u,v}) :
    LoopCircle ≃ₜ Metric.sphere (0:ℂ) 1 := by
  let f := planarPrimitiveLoop C (C.boundary.curve C.waist)
  let q : LoopCircle → Metric.sphere (0:ℂ) 1 := fun z => ⟨f.circleMap z,by
    rw [←canonical_waist_planar_trace C,←loop_circleMap_range_eq_trace]
    exact ⟨z,rfl⟩⟩
  have he : Topology.IsEmbedding q :=
    (Topology.IsEmbedding.of_comp_iff (f := q)
      (g := (Subtype.val : Metric.sphere (0:ℂ) 1 → ℂ)) .subtypeVal).mp
        (simple_loop_circleMap_embedding f
          (planarPrimitiveLoop_simple C (C.boundary.curve C.waist) (canonical_waist_simple C))).isEmbedding
  apply he.toHomeomorphOfSurjective
  intro z
  have hz : z.val ∈ f.trace := by rw [canonical_waist_planar_trace];exact z.property
  rw [←loop_circleMap_range_eq_trace] at hz
  obtain ⟨w,hw⟩ := hz
  exact ⟨w,Subtype.ext hw⟩

lemma waistCircleHomeomorph_apply (C : Chart.{u,v}) (z : LoopCircle) :
    (waistCircleHomeomorph C z).val =
      (planarPrimitiveLoop C (C.boundary.curve C.waist)).circleMap z := rfl

def canonicalWaistDisk (C : Chart.{u,v}) :
    DiskBoundedBy (planarPrimitiveLoop C (C.boundary.curve C.waist)) where
  map := ⟨Subtype.val,continuous_subtype_val⟩
  embedding := .subtypeVal
  circle := waistCircleHomeomorph C
  boundary := waistCircleHomeomorph_apply C
  inner_open := by
    have he : (Subtype.val : ClosedDisk → ℂ) '' {z : ClosedDisk | dist z.val 0 < 1} =
        Metric.ball (0:ℂ) 1 := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact hw
      · intro hz
        change dist z 0 < 1 at hz
        exact ⟨⟨z,show dist z 0 ≤ 1 from hz.le⟩,hz,rfl⟩
    change IsOpen ((Subtype.val : ClosedDisk → ℂ) '' _)
    rw [he]
    exact Metric.isOpen_ball
  frontier_eq := by
    change frontier (Set.range (Subtype.val : ClosedDisk → ℂ)) = _
    rw [Subtype.range_val]
    change frontier (Metric.closedBall (0:ℂ) 1) = _
    rw [frontier_closedBall (0:ℂ) (by norm_num : (1:ℝ) ≠ 0),canonical_waist_planar_trace]

lemma canonicalWaistDisk_range (C : Chart.{u,v}) :
    Set.range (canonicalWaistDisk C).map = Metric.closedBall (0:ℂ) 1 :=
  Subtype.range_val


def canonicalDiskAnnulus (C : Chart.{u,v}) (γ : C.model.curves.Primitive)
    (D : DiskBoundedBy (planarPrimitiveLoop C γ))
    (hp : (1/2:ℂ) ∈ interior (Set.range D.map))
    (hm : -(1/2:ℂ) ∈ interior (Set.range D.map))
    (A : AnnulusBetween (planarPrimitiveLoop C γ)
      (planarPrimitiveLoop C (C.boundary.curve C.waist)))
    (hA : Set.range A.map = Metric.closedBall (0:ℂ) 1 \
      interior (Set.range D.map)) :
    AnnulusBetween (primitiveLoop C.model (γ))
      (primitiveLoop C.model (C.boundary.curve C.waist)) := by
  have hAz (z : LoopCircle × unitInterval) :
      ‖A.map z‖ ≤ 1 ∧ A.map z ≠ (1/2:ℂ) ∧ A.map z ≠ -(1/2:ℂ) := by
    have hz : A.map z ∈ Metric.closedBall (0:ℂ) 1 \
        interior (Set.range D.map) := by rw [←hA];exact ⟨z,rfl⟩
    refine ⟨?_,?_,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
    · intro he
      exact hz.2 (he ▸ hp)
    · intro he
      exact hz.2 (he ▸ hm)
  let map : C(LoopCircle × unitInterval,C.model.surface.Point) :=
    ⟨fun z => C.topology.symm ⟨A.map z,hAz z⟩,
      C.topology.symm.continuous.comp (A.map.continuous.subtype_mk _)⟩
  have hmap (z : LoopCircle × unitInterval) : pantsPlanarChart C (map z) = A.map z := by
    change (C.topology (C.topology.symm _)).val = _
    rw [Homeomorph.apply_symm_apply]
  refine {
    map := map
    injective := ?_
    endReparam := A.endReparam
    boundary_zero := ?_
    boundary_one := ?_ }
  · intro z w he
    apply A.injective
    have h := congrArg (pantsPlanarChart C) he
    simpa only [hmap] using h
  · intro z
    apply pantsPlanarChart_injective C
    rw [hmap,A.boundary_zero]
    exact mapClosedLoop_circleMap (pantsPlanarChart C) _ z
  · intro z
    apply pantsPlanarChart_injective C
    rw [hmap,A.boundary_one]
    exact mapClosedLoop_circleMap (pantsPlanarChart C) _ (A.endReparam z)

lemma canonical_nonwaist_not_simple (C : Chart.{u,v})
    (BC : PrimitiveBoundaryClassics C.model C.boundary)
    (LS : BorderedLoopStraighteningClassics C.model C.boundary)
    (J : WP.External.PlanarJordanGeometry.PlanarJordanClassics)
    (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics C.model C.boundary)
    (γ : C.model.curves.Primitive) (hγ : γ ≠ (C.boundary.curve C.waist)) :
    ¬ SimpleTrace C.model (γ) := by
  intro hs
  obtain ⟨D⟩ := planarPrimitiveLoop_has_boundedDisk C J γ hs
  have hboth := canonical_nonwaist_JordanDisk_contains_both_punctures C BC LS PC PP γ hγ D
  have hD := planarPrimitiveLoop_boundedDisk_inside_unitDisk C BC γ hγ D
  have hsub : Set.range D.map ⊆ interior (Set.range (canonicalWaistDisk C).map) := by
    rw [canonicalWaistDisk_range,interior_closedBall (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)]
    intro z hz
    simpa only [Metric.mem_ball,dist_zero_right] using hD z hz
  obtain ⟨A,hA⟩ := PC.nested_annulus D (canonicalWaistDisk C) hsub
  rw [canonicalWaistDisk_range] at hA
  let E := canonicalDiskAnnulus C γ D hboth.1 hboth.2 A hA
  have hwaist : C.model.curves.trace (C.boundary.curve C.waist) ⊆ Set.range E.map := by
    rw [←WP.Critical.ShortConfiguration.primitiveLoop_trace]
    exact annulus_trace_right_subset E
  have hclass := PP.annulus_axial_class _ _ E (C.boundary.curve C.waist)
    (WP.Critical.ShortConfiguration.primitiveLoop_simple _ _ hs)
    (bordered_primitive_positiveHomotopyLength _ _ LS _) hwaist
  exact hγ ((LS.class_eq _ _).mp hclass).symm

lemma canonical_simple_iff_waist (C : Chart.{u,v})
    (BC : PrimitiveBoundaryClassics C.model C.boundary)
    (LS : BorderedLoopStraighteningClassics C.model C.boundary)
    (J : WP.External.PlanarJordanGeometry.PlanarJordanClassics)
    (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics C.model C.boundary)
    (γ : C.model.curves.Primitive) :
    SimpleTrace C.model (γ) ↔ γ = (C.boundary.curve C.waist) := by
  constructor
  · intro hs
    by_contra hn
    exact canonical_nonwaist_not_simple C BC LS J PC PP γ hn hs
  · rintro rfl
    exact canonical_waist_simple C


end WP.Critical.PantsCluster.GenericPants

namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry
open WP.External.PlanarJordanGeometry WP.External.PlanarRegionGeometry
open WP.External.ShortBorderedPeripheralGeometry

lemma actual_pants_simple_iff_boundary (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) (R : BoundaryRealization B) (hb : B.boundaries = 1)
    (BC : PrimitiveBoundaryClassics B R) (LS : BorderedLoopStraighteningClassics B R)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics B R) (γ : B.curves.Primitive)
    (j : Fin B.boundaries) : SimpleTrace B γ ↔ γ = R.curve j := by
  obtain ⟨e,he⟩ := hp
  let C : GenericPants.Chart := ⟨B,e,he,R,hb,j⟩
  exact GenericPants.canonical_simple_iff_waist C BC LS J PC PP γ

end WP.Critical.PantsCluster
