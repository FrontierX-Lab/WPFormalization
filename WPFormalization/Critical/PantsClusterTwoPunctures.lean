import WPFormalization.Critical.PantsClusterOnePuncture
import WPFormalization.Critical.PantsClusterWaistDisk

/-! The two-puncture case is an actual annulus up to the actual waist.
Generic planar topology and generic primitive annulus classes therefore imply,
locally, that the only simple primitive on canonical pants is the waist. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry Set
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry

lemma annulus_trace_left_subset {X : Type*} [TopologicalSpace X] {f g : ClosedLoop X}
    (A : AnnulusBetween f g) : f.trace ⊆ Set.range A.map := by
  rw [←loop_circleMap_range_eq_trace]
  rintro _ ⟨z,rfl⟩
  exact ⟨(z,0),A.boundary_zero z⟩

lemma annulus_trace_right_subset {X : Type*} [TopologicalSpace X] {f g : ClosedLoop X}
    (A : AnnulusBetween f g) : g.trace ⊆ Set.range A.map := by
  rw [←loop_circleMap_range_eq_trace]
  rintro _ ⟨z,rfl⟩
  exact ⟨(A.endReparam.symm z,1),by rw [A.boundary_one,A.endReparam.apply_symm_apply]⟩

def canonicalDiskAnnulus (F : Family.{u,v}) (s : Waist) (γ : F.Primitive)
    (D : DiskBoundedBy (planarPrimitiveLoop F s γ))
    (hp : (1/2:ℂ) ∈ interior (Set.range D.map))
    (hm : -(1/2:ℂ) ∈ interior (Set.range D.map))
    (A : AnnulusBetween (planarPrimitiveLoop F s γ)
      (planarPrimitiveLoop F s F.waistClass))
    (hA : Set.range A.map = Metric.closedBall (0:ℂ) 1 \
      interior (Set.range D.map)) :
    AnnulusBetween (primitiveLoop (F.model s) (F.marking s γ))
      (primitiveLoop (F.model s) (F.marking s F.waistClass)) := by
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
  let map : C(LoopCircle × unitInterval,(F.model s).surface.Point) :=
    ⟨fun z => (F.topology s).symm ⟨A.map z,hAz z⟩,
      (F.topology s).symm.continuous.comp (A.map.continuous.subtype_mk _)⟩
  have hmap (z : LoopCircle × unitInterval) : pantsPlanarChart F s (map z) = A.map z := by
    change ((F.topology s) ((F.topology s).symm _)).val = _
    rw [Homeomorph.apply_symm_apply]
  refine {
    map := map
    injective := ?_
    endReparam := A.endReparam
    boundary_zero := ?_
    boundary_one := ?_ }
  · intro z w he
    apply A.injective
    have h := congrArg (pantsPlanarChart F s) he
    simpa only [hmap] using h
  · intro z
    apply pantsPlanarChart_injective F s
    rw [hmap,A.boundary_zero]
    exact mapClosedLoop_circleMap (pantsPlanarChart F s) _ z
  · intro z
    apply pantsPlanarChart_injective F s
    rw [hmap,A.boundary_one]
    exact mapClosedLoop_circleMap (pantsPlanarChart F s) _ (A.endReparam z)

lemma canonical_nonwaist_not_simple (F : Family.{u,v}) (s : Waist)
    (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : WP.External.PlanarJordanGeometry.PlanarJordanClassics)
    (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) (hγ : γ ≠ F.waistClass) :
    ¬ SimpleTrace (F.model s) (F.marking s γ) := by
  intro hs
  obtain ⟨D⟩ := planarPrimitiveLoop_has_boundedDisk F s J γ hs
  have hboth := canonical_nonwaist_JordanDisk_contains_both_punctures F s BC LS PC PP γ hγ D
  have hD := planarPrimitiveLoop_boundedDisk_inside_unitDisk F s BC γ hγ D
  have hsub : Set.range D.map ⊆ interior (Set.range (canonicalWaistDisk F s).map) := by
    rw [canonicalWaistDisk_range,interior_closedBall (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)]
    intro z hz
    simpa only [Metric.mem_ball,dist_zero_right] using hD z hz
  obtain ⟨A,hA⟩ := PC.nested_annulus D (canonicalWaistDisk F s) hsub
  rw [canonicalWaistDisk_range] at hA
  let E := canonicalDiskAnnulus F s γ D hboth.1 hboth.2 A hA
  have hwaist : (F.model s).curves.trace (F.marking s F.waistClass) ⊆ Set.range E.map := by
    rw [←WP.Critical.ShortConfiguration.primitiveLoop_trace]
    exact annulus_trace_right_subset E
  have hclass := PP.annulus_axial_class _ _ E (F.marking s F.waistClass)
    (WP.Critical.ShortConfiguration.primitiveLoop_simple _ _ hs)
    (bordered_primitive_positiveHomotopyLength _ _ LS _) hwaist
  exact hγ ((F.marking s).injective ((LS.class_eq _ _).mp hclass).symm)

lemma canonical_simple_iff_waist (F : Family.{u,v}) (s : Waist)
    (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : WP.External.PlanarJordanGeometry.PlanarJordanClassics)
    (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) :
    SimpleTrace (F.model s) (F.marking s γ) ↔ γ = F.waistClass := by
  constructor
  · intro hs
    by_contra hn
    exact canonical_nonwaist_not_simple F s BC LS J PC PP γ hn hs
  · rintro rfl
    exact canonical_waist_simple F s

end WP.Critical.PantsCluster
