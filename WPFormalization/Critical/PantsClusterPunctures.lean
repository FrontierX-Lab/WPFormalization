import WPFormalization.Critical.PantsClusterPlanarChart

/-! A nonwaist primitive's actual Jordan disk cannot enclose zero punctures.
The proof transports a puncture-free disk to the actual pants and applies
the proved generic disk contraction, with generic bordered length minimality. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry Set

lemma boundedDisk_trace_subset {X : Type*} [MetricSpace X] {f : ClosedLoop X}
    (D : DiskBoundedBy f) : f.trace ⊆ Set.range D.map := by
  rw [←loop_circleMap_range_eq_trace]
  rintro _ ⟨z,rfl⟩
  exact ⟨⟨(D.circle z).val,le_of_eq (D.circle z).property⟩,D.boundary z⟩

lemma canonical_nonwaist_JordanDisk_contains_puncture (F : Family.{u,v}) (s : Waist)
    (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) (hγ : γ ≠ F.waistClass)
    (D : DiskBoundedBy (planarPrimitiveLoop F s γ)) :
    (1/2:ℂ) ∈ Set.range D.map ∨ -(1/2:ℂ) ∈ Set.range D.map := by
  by_contra hn
  rcases not_or.mp hn with ⟨hp,hm⟩
  have hf : ∀ t, (planarPrimitiveLoop F s γ).map t ∈ openPantsDisk := by
    intro t
    exact ⟨planarPrimitiveLoop_nonwaist_inside_unitDisk F s BC γ hγ _ ⟨t,rfl⟩,
      planarPrimitiveLoop_avoids_punctures F s γ _ ⟨t,rfl⟩⟩
  have hD : ∀ z, D.map z ∈ openPantsDisk := by
    intro z
    refine ⟨planarPrimitiveLoop_boundedDisk_inside_unitDisk F s BC γ hγ D _ ⟨z,rfl⟩,?_,?_⟩
    · intro hz
      exact hp ⟨z,hz⟩
    · intro hz
      exact hm ⟨z,hz⟩
  let E := boundedDisk_liftOpen openPantsDisk openPantsDisk_isOpen D hf hD
  let R := boundedDisk_mapOpenEmbedding (openPantsDiskToSurface F s)
    (openPantsDiskToSurface_isOpenEmbedding F s) E
  have he : mapClosedLoop (openPantsDiskToSurface F s)
      (subtypeClosedLoop openPantsDisk (planarPrimitiveLoop F s γ) hf) =
        primitiveLoop (F.model s) (F.marking s γ) := by
    apply WP.Critical.ShortConfiguration.ClosedLoop.ext_map
    ext t
    apply pantsPlanarChart_injective F s
    change pantsPlanarChart F s (openPantsDiskToSurface F s _) =
      pantsPlanarChart F s ((primitiveLoop (F.model s) (F.marking s γ)).map t)
    rw [pantsPlanarChart_openPantsDiskToSurface]
    rfl
  have hR : DiskBoundedBy (primitiveLoop (F.model s) (F.marking s γ)) := he ▸ R
  exact WP.Critical.ShortConfiguration.ClosedLoop.not_positive_of_nullhomotopic _
    (WP.Critical.ShortConfiguration.disk_loop_nullhomotopic hR _ (boundedDisk_trace_subset hR))
    (bordered_primitive_positiveHomotopyLength (F.model s) (F.boundary s) LS (F.marking s γ))

end WP.Critical.PantsCluster
