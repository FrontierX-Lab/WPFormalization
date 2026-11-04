import WPFormalization.Critical.PantsClusterDiskRegions
import WPFormalization.External.ShortBorderedPeripheralGeometry

/-! An actual Jordan disk containing exactly one of the two missing points
would be an actual peripheral half-cylinder in the pants. Generic parabolic
versus axial theory excludes that case; it is not a field of the pants family. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry Set
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry

lemma cuspEnd_trace_subset {X : Type*} [MetricSpace X] {f : ClosedLoop X}
    (E : CuspEndBoundedBy f) : f.trace ⊆ Set.range E.map := by
  rw [←loop_circleMap_range_eq_trace]
  rintro _ ⟨z,rfl⟩
  exact ⟨(z,⟨0,by simp⟩),E.boundary z⟩

def canonicalPuncturedDiskCuspEnd (F : Family.{u,v}) (s : Waist)
    (γ : F.Primitive) (D : DiskBoundedBy (planarPrimitiveLoop F s γ)) (p : ℂ)
    (hp : p = (1/2:ℂ) ∨ p = -(1/2:ℂ))
    (hD : ∀ z ∈ Set.range D.map, ‖z‖ < 1)
    (hother : ∀ z ∈ Set.range D.map, z ≠ p → z ≠ (1/2:ℂ) ∧ z ≠ -(1/2:ℂ))
    (K : PuncturedDiskCoordinates D p) :
    CuspEndBoundedBy (primitiveLoop (F.model s) (F.marking s γ)) := by
  let e := K.coordinates.trans (puncturedDisk_pantsRegionHomeomorph F s D p hp hD hother)
  let map : C(LoopCircle × Ici (0:ℝ),(F.model s).surface.Point) :=
    ⟨fun z => (e z).val,continuous_subtype_val.comp e.continuous⟩
  have hmap (w : LoopCircle × Ici (0:ℝ)) :
      pantsPlanarChart F s (map w) = (K.coordinates w).val := by
    exact puncturedDisk_pantsRegionHomeomorph_apply_chart F s D p hp hD hother (K.coordinates w)
  have hrange : Set.range map = pantsPlanarChart F s ⁻¹' Set.range D.map := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩
      exact (e w).property
    · intro hz
      exact ⟨e.symm ⟨z,hz⟩,by simp only [map,ContinuousMap.coe_mk,e.apply_symm_apply]⟩
  have hinner : map '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val} =
      pantsPlanarChart F s ⁻¹' interior (Set.range D.map) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      have hK := show K.coordinates w ∈
          K.coordinates '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val} from ⟨w,hw,rfl⟩
      rw [K.inner_range] at hK
      change pantsPlanarChart F s (map w) ∈ interior (Set.range D.map)
      rw [hmap]
      exact hK
    · intro hz
      have hDz : pantsPlanarChart F s z ∈ Set.range D.map := interior_subset hz
      have hneq : pantsPlanarChart F s z ≠ p := by
        rcases hp with rfl|rfl
        · exact ((F.topology s z).property).2.1
        · exact ((F.topology s z).property).2.2
      have hK : (⟨pantsPlanarChart F s z,hDz,hneq⟩ :
          {z : ℂ // z ∈ Set.range D.map ∧ z ≠ p}) ∈
          K.coordinates '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val} := by
        rw [K.inner_range]
        exact hz
      obtain ⟨w,hw,hew⟩ := hK
      refine ⟨w,hw,?_⟩
      apply pantsPlanarChart_injective F s
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
    exact (boundedDisk_range_isCompact D).isClosed.preimage (pantsPlanarChart F s).continuous
  · intro z
    apply pantsPlanarChart_injective F s
    rw [hmap,K.boundary]
    exact mapClosedLoop_circleMap (pantsPlanarChart F s) _ z
  · rw [hinner]
    exact isOpen_interior.preimage (pantsPlanarChart F s).continuous
  · rw [hrange,pants_chart_disk_region_frontier F s γ D hD,
      WP.Critical.ShortConfiguration.primitiveLoop_trace]

lemma canonical_JordanDisk_not_one_puncture (F : Family.{u,v}) (s : Waist)
    (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) (D : DiskBoundedBy (planarPrimitiveLoop F s γ)) (p : ℂ)
    (hp : p = (1/2:ℂ) ∨ p = -(1/2:ℂ)) (hpD : p ∈ Set.range D.map)
    (hD : ∀ z ∈ Set.range D.map, ‖z‖ < 1)
    (hother : ∀ z ∈ Set.range D.map, z ≠ p → z ≠ (1/2:ℂ) ∧ z ≠ -(1/2:ℂ)) : False := by
  obtain ⟨K⟩ := PC.punctured_disk D p (canonical_puncture_mem_disk_interior F s γ D hp hpD)
  let E := canonicalPuncturedDiskCuspEnd F s γ D p hp hD hother K
  apply PP.cusp_no_axial _ E (F.marking s γ)
  rw [←WP.Critical.ShortConfiguration.primitiveLoop_trace]
  exact cuspEnd_trace_subset E

lemma canonical_nonwaist_JordanDisk_contains_both_punctures (F : Family.{u,v})
    (s : Waist) (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) (hγ : γ ≠ F.waistClass)
    (D : DiskBoundedBy (planarPrimitiveLoop F s γ)) :
    (1/2:ℂ) ∈ interior (Set.range D.map) ∧
      -(1/2:ℂ) ∈ interior (Set.range D.map) := by
  have hD := planarPrimitiveLoop_boundedDisk_inside_unitDisk F s BC γ hγ D
  have he := canonical_nonwaist_JordanDisk_contains_puncture F s BC LS γ hγ D
  have hboth : (1/2:ℂ) ∈ Set.range D.map ∧ -(1/2:ℂ) ∈ Set.range D.map := by
    rcases he with hp|hm
    · refine ⟨hp,?_⟩
      by_contra hn
      apply canonical_JordanDisk_not_one_puncture F s PC PP γ D (1/2:ℂ) (Or.inl rfl) hp hD
      intro z hz hzp
      exact ⟨hzp,fun hzm => hn (hzm ▸ hz)⟩
    · refine ⟨?_,hm⟩
      by_contra hn
      apply canonical_JordanDisk_not_one_puncture F s PC PP γ D (-(1/2:ℂ)) (Or.inr rfl) hm hD
      intro z hz hzm
      exact ⟨fun hzp => hn (hzp ▸ hz),hzm⟩
  exact ⟨canonical_puncture_mem_disk_interior F s γ D (Or.inl rfl) hboth.1,
    canonical_puncture_mem_disk_interior F s γ D (Or.inr rfl) hboth.2⟩

end WP.Critical.PantsCluster
