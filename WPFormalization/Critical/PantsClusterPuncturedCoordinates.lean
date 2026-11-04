import WPFormalization.Critical.PantsClusterRegionTransport
import WPFormalization.External.PlanarRegionGeometry

/-! A generic punctured Jordan disk becomes a literal properly embedded
peripheral-end region in the punctured plane. The classical input is only
ordinary planar coordinates; all frontier and properness properties are proved. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace WP.Critical.PantsCluster
open Set WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortComplementaryRegionGeometry WP.External.PlanarRegionGeometry

def puncturedCoordinates_cuspEnd {f : ClosedLoop ℂ} (D : DiskBoundedBy f)
    (p : ℂ) (hf : ∀ t, f.map t ≠ p) (K : PuncturedDiskCoordinates D p) :
    CuspEndBoundedBy (subtypeClosedLoop {z : ℂ | z ≠ p} f hf) := by
  let U : Set ℂ := {z | z ≠ p}
  let V : Set U := {z | z.val ∈ Set.range D.map}
  let e : {z : ℂ // z ∈ Set.range D.map ∧ z ≠ p} ≃ₜ V := {
    toFun := fun z => ⟨⟨z.val,z.property.2⟩,z.property.1⟩
    invFun := fun z => ⟨z.val.val,z.property,z.val.property⟩
    left_inv := fun z => rfl
    right_inv := fun z => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let q := K.coordinates.trans e
  let map : C(LoopCircle × Ici (0:ℝ),U) :=
    ⟨fun z => (q z).val,continuous_subtype_val.comp q.continuous⟩
  have hrange : Set.range map = V := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩
      exact (q w).property
    · intro hz
      exact ⟨q.symm ⟨z,hz⟩,by simpa only [map,ContinuousMap.coe_mk,q.apply_symm_apply]⟩
  have hinner : map '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val} =
      Subtype.val ⁻¹' interior (Set.range D.map) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      have := show K.coordinates w ∈
          K.coordinates '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val} from ⟨w,hw,rfl⟩
      rw [K.inner_range] at this
      exact this
    · intro hz
      have hDz : z.val ∈ Set.range D.map := interior_subset hz
      have hK : (⟨z.val,hDz,z.property⟩ :
          {z : ℂ // z ∈ Set.range D.map ∧ z ≠ p}) ∈
          K.coordinates '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val} := by
        rw [K.inner_range]
        exact hz
      obtain ⟨w,hw,hew⟩ := hK
      refine ⟨w,hw,?_⟩
      apply Subtype.ext
      change (K.coordinates w).val = z.val
      exact congrArg (fun v : {z : ℂ // z ∈ Set.range D.map ∧ z ≠ p} => v.val) hew
  refine {
    map := map
    closedEmbedding := ⟨?_,?_⟩
    boundary := ?_
    inner_open := ?_
    frontier_eq := ?_ }
  · exact Topology.IsEmbedding.subtypeVal.comp q.isEmbedding
  · rw [hrange]
    exact (boundedDisk_range_isCompact D).isClosed.preimage continuous_subtype_val
  · intro z
    apply Subtype.ext
    change (K.coordinates (z,⟨0,by simp⟩)).val = _
    rw [K.boundary,subtypeClosedLoop_circleMap]
  · rw [hinner]
    exact isOpen_interior.preimage continuous_subtype_val
  · rw [hrange]
    change frontier (Subtype.val ⁻¹' Set.range D.map) = _
    rw [←(isOpen_ne : IsOpen U).isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val,D.frontier_eq,subtypeClosedLoop_trace]

end WP.Critical.PantsCluster
