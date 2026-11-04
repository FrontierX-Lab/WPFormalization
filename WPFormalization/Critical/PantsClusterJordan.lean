import WPFormalization.Critical.PantsClusterLoopTopology
import WPFormalization.Critical.ShortConfigurationBoundaryCycles
import WPFormalization.External.PlanarJordanGeometry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! A generic actual simple plane loop bounds an actual embedded disk.
Only the old planar Jordan--Schoenflies extension is classical input. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace WP.Critical.PantsCluster
open Set WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortComplementaryRegionGeometry WP.External.PlanarJordanGeometry

def loopCircleHomeomorphSphere : LoopCircle ≃ₜ Metric.sphere (0 : ℂ) 1 :=
  WP.Critical.ShortConfiguration.loopCircleHomeomorphAddCircle.trans
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero)

lemma loop_circleMap_range_eq_trace {X : Type*} [TopologicalSpace X]
    (f : ClosedLoop X) : Set.range f.circleMap = f.trace := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    refine Quot.inductionOn q (fun t => ?_)
    exact ⟨t,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨Quot.mk loopCircleEndpoint t,rfl⟩

lemma simple_plane_loop_boundedDisk (J : PlanarJordanClassics)
    (f : ClosedLoop ℂ) (hf : f.Simple) : Nonempty (DiskBoundedBy f) := by
  let c := loopCircleHomeomorphSphere
  let g : C(Metric.sphere (0 : ℂ) 1, ℂ) :=
    f.circleMap.comp ⟨c.symm,c.symm.continuous⟩
  have hg : Function.Injective g :=
    (simple_loop_circleMap_injective f hf).comp c.symm.injective
  obtain ⟨e,he⟩ := J.extend_circle g hg
  have he' (z : Metric.sphere (0 : ℂ) 1) : e z.val = f.circleMap (c.symm z) := he z
  let map : C(ClosedDisk, ℂ) :=
    ⟨fun z => e z.val,e.continuous.comp continuous_subtype_val⟩
  have hecircle : e '' Metric.sphere (0 : ℂ) 1 = f.trace := by
    rw [←loop_circleMap_range_eq_trace]
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨c.symm ⟨z,hz⟩,(he' ⟨z,hz⟩).symm⟩
    · rintro ⟨z,rfl⟩
      refine ⟨(c z).val,(c z).property,?_⟩
      simpa only [Homeomorph.symm_apply_apply] using he' (c z)
  have hinner : map '' {z : ClosedDisk | dist z.val 0 < 1} =
      e '' Metric.ball (0 : ℂ) 1 := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      refine ⟨⟨z,?_⟩,hz,rfl⟩
      change dist z 0 ≤ 1
      exact hz.le
  have hrange : Set.range map = e '' Metric.closedBall (0 : ℂ) 1 := by
    ext p
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z.val,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,rfl⟩
  refine ⟨{
    map := map
    embedding := e.isEmbedding.comp (.subtypeVal)
    circle := c
    boundary := ?_
    inner_open := ?_
    frontier_eq := ?_ }⟩
  · intro z
    change e (c z).val = f.circleMap z
    simpa only [Homeomorph.symm_apply_apply] using he' (c z)
  · rw [hinner]
    exact e.isOpenMap _ Metric.isOpen_ball
  · rw [hrange,←e.image_frontier,frontier_closedBall _ (by norm_num : (1:ℝ) ≠ 0)]
    exact hecircle

end WP.Critical.PantsCluster
