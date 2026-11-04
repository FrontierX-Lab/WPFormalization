import WPFormalization.Critical.PantsClusterPuncturedCoordinates

/-! The actual disk region in the canonical pants chart, including its
relative frontier. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry Set

lemma pants_chart_disk_region_frontier (F : Family.{u,v}) (s : Waist)
    (γ : F.Primitive) (D : DiskBoundedBy (planarPrimitiveLoop F s γ))
    (hD : ∀ z ∈ Set.range D.map, ‖z‖ < 1) :
    frontier (pantsPlanarChart F s ⁻¹' Set.range D.map) =
      (F.model s).curves.trace (F.marking s γ) := by
  let A : Set openPantsDisk := Subtype.val ⁻¹' Set.range D.map
  let h := openPantsDiskToSurface F s
  have hi : ∀ p, p ∈ pantsPlanarChart F s ⁻¹' Set.range D.map →
      p ∈ intrinsicInterior (F.model s) := by
    intro p hp
    exact (canonical_pants_interior_iff F s p).mpr (hD _ hp)
  have hrange : h '' A = pantsPlanarChart F s ⁻¹' Set.range D.map := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      change pantsPlanarChart F s (openPantsDiskToSurface F s z) ∈ Set.range D.map
      rwa [pantsPlanarChart_openPantsDiskToSurface]
    · intro hp
      have := hi p hp
      rw [←openPantsDiskToSurface_range] at this
      obtain ⟨z,rfl⟩ := this
      refine ⟨z,?_,rfl⟩
      change z.val ∈ Set.range D.map
      rw [←pantsPlanarChart_openPantsDiskToSurface F s z]
      exact hp
  have hclosed : IsClosed (h '' A) := by
    rw [hrange]
    exact (boundedDisk_range_isCompact D).isClosed.preimage (pantsPlanarChart F s).continuous
  rw [←hrange,openEmbedding_image_frontier_of_closed_image
    (openPantsDiskToSurface_isOpenEmbedding F s) A hclosed]
  have hfront : frontier A = Subtype.val ⁻¹' (planarPrimitiveLoop F s γ).trace := by
    change frontier (Subtype.val ⁻¹' Set.range D.map) = _
    rw [←openPantsDisk_isOpen.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val,D.frontier_eq]
  rw [hfront]
  ext p
  constructor
  · rintro ⟨z,hz,rfl⟩
    rw [planarPrimitiveLoop_trace] at hz
    obtain ⟨q,hq,heq⟩ := hz
    have hh : openPantsDiskToSurface F s z = q := by
      apply pantsPlanarChart_injective F s
      rw [pantsPlanarChart_openPantsDiskToSurface]
      exact heq.symm
    simpa only [h,hh] using hq
  · intro hp
    have hz : pantsPlanarChart F s p ∈ Set.range D.map :=
      boundedDisk_trace_subset D (by rw [planarPrimitiveLoop_trace];exact ⟨p,hp,rfl⟩)
    let z : openPantsDisk := ⟨pantsPlanarChart F s p,hD _ hz,
      ((F.topology s p).property).2⟩
    refine ⟨z,?_,?_⟩
    · change z.val ∈ (planarPrimitiveLoop F s γ).trace
      rw [planarPrimitiveLoop_trace]
      exact ⟨p,hp,rfl⟩
    · apply pantsPlanarChart_injective F s
      exact pantsPlanarChart_openPantsDiskToSurface F s z

def puncturedDisk_pantsRegionHomeomorph (F : Family.{u,v}) (s : Waist)
    {f : ClosedLoop ℂ} (D : DiskBoundedBy f) (p : ℂ)
    (hp : p = (1/2:ℂ) ∨ p = -(1/2:ℂ))
    (hD : ∀ z ∈ Set.range D.map, ‖z‖ < 1)
    (hother : ∀ z ∈ Set.range D.map, z ≠ p → z ≠ (1/2:ℂ) ∧ z ≠ -(1/2:ℂ)) :
    {z : ℂ // z ∈ Set.range D.map ∧ z ≠ p} ≃ₜ
      {x : (F.model s).surface.Point // pantsPlanarChart F s x ∈ Set.range D.map} where
  toFun z := ⟨(F.topology s).symm
    ⟨z.val,(hD z.val z.property.1).le,hother _ z.property.1 z.property.2⟩,by
      change pantsPlanarChart F s ((F.topology s).symm _) ∈ _
      simpa only [pantsPlanarChart,ContinuousMap.coe_mk,Homeomorph.apply_symm_apply]
        using z.property.1⟩
  invFun x := ⟨pantsPlanarChart F s x.val,x.property,by
    rcases hp with rfl|rfl
    · exact ((F.topology s x.val).property).2.1
    · exact ((F.topology s x.val).property).2.2⟩
  left_inv z := by apply Subtype.ext; simp [pantsPlanarChart]
  right_inv x := by apply Subtype.ext; exact (F.topology s).symm_apply_apply x.val
  continuous_toFun := by fun_prop
  continuous_invFun := by
    exact ((pantsPlanarChart F s).continuous.comp continuous_subtype_val).subtype_mk _

lemma puncturedDisk_pantsRegionHomeomorph_apply_chart (F : Family.{u,v}) (s : Waist)
    {f : ClosedLoop ℂ} (D : DiskBoundedBy f) (p : ℂ)
    (hp : p = (1/2:ℂ) ∨ p = -(1/2:ℂ))
    (hD : ∀ z ∈ Set.range D.map, ‖z‖ < 1)
    (hother : ∀ z ∈ Set.range D.map, z ≠ p → z ≠ (1/2:ℂ) ∧ z ≠ -(1/2:ℂ))
    (z : {z : ℂ // z ∈ Set.range D.map ∧ z ≠ p}) :
    pantsPlanarChart F s ((puncturedDisk_pantsRegionHomeomorph F s D p hp hD hother z).val) =
      z.val := by
  change ((F.topology s) ((F.topology s).symm _)).val = z.val
  rw [Homeomorph.apply_symm_apply]

end WP.Critical.PantsCluster
