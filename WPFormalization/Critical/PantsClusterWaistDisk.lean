import WPFormalization.Critical.PantsClusterDiskInterior

/-! The actual waist maps onto the full unit circle, so the standard closed
unit disk supplies its outer Jordan disk without any arbitrary kernel choice. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry Set

lemma canonical_waist_trace_eq_boundary (F : Family.{u,v}) (s : Waist) :
    (F.model s).curves.trace (F.marking s F.waistClass) = intrinsicBoundary (F.model s) := by
  unfold Family.waistClass
  rw [F.marking_waist,←(F.boundary s).cover]
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · exact fun hp => ⟨F.waist s,hp⟩
  · rintro ⟨j,hj⟩
    rwa [canonical_boundary_index_eq F s j] at hj

lemma canonical_waist_planar_trace (F : Family.{u,v}) (s : Waist) :
    (planarPrimitiveLoop F s F.waistClass).trace = Metric.sphere (0:ℂ) 1 := by
  rw [planarPrimitiveLoop_trace,canonical_waist_trace_eq_boundary]
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    simpa only [Metric.mem_sphere,dist_zero_right,pantsPlanarChart,ContinuousMap.coe_mk] using (F.topological_boundary s p).mp hp
  · intro hz
    have hn : ‖z‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hz
    have hp : z ≠ (1/2:ℂ) := by intro h;rw [h] at hn;norm_num at hn
    have hm : z ≠ -(1/2:ℂ) := by intro h;rw [h] at hn;norm_num at hn
    let p := (F.topology s).symm ⟨z,hn.le,hp,hm⟩
    refine ⟨p,?_,?_⟩
    · apply (F.topological_boundary s p).mpr
      simp only [p,Homeomorph.apply_symm_apply]
      exact hn
    · change ((F.topology s) ((F.topology s).symm _)).val = z
      simp only [Homeomorph.apply_symm_apply]

lemma canonical_waist_simple (F : Family.{u,v}) (s : Waist) :
    SimpleTrace (F.model s) (F.marking s F.waistClass) := by
  unfold Family.waistClass
  rw [F.marking_waist]
  exact (F.boundary s).simple (F.waist s)

def waistCircleHomeomorph (F : Family.{u,v}) (s : Waist) :
    LoopCircle ≃ₜ Metric.sphere (0:ℂ) 1 := by
  let f := planarPrimitiveLoop F s F.waistClass
  let q : LoopCircle → Metric.sphere (0:ℂ) 1 := fun z => ⟨f.circleMap z,by
    rw [←canonical_waist_planar_trace F s,←loop_circleMap_range_eq_trace]
    exact ⟨z,rfl⟩⟩
  have he : Topology.IsEmbedding q :=
    (Topology.IsEmbedding.of_comp_iff (f := q)
      (g := (Subtype.val : Metric.sphere (0:ℂ) 1 → ℂ)) .subtypeVal).mp
        (simple_loop_circleMap_embedding f
          (planarPrimitiveLoop_simple F s F.waistClass (canonical_waist_simple F s))).isEmbedding
  apply he.toHomeomorphOfSurjective
  intro z
  have hz : z.val ∈ f.trace := by rw [canonical_waist_planar_trace];exact z.property
  rw [←loop_circleMap_range_eq_trace] at hz
  obtain ⟨w,hw⟩ := hz
  exact ⟨w,Subtype.ext hw⟩

lemma waistCircleHomeomorph_apply (F : Family.{u,v}) (s : Waist) (z : LoopCircle) :
    (waistCircleHomeomorph F s z).val =
      (planarPrimitiveLoop F s F.waistClass).circleMap z := rfl

def canonicalWaistDisk (F : Family.{u,v}) (s : Waist) :
    DiskBoundedBy (planarPrimitiveLoop F s F.waistClass) where
  map := ⟨Subtype.val,continuous_subtype_val⟩
  embedding := .subtypeVal
  circle := waistCircleHomeomorph F s
  boundary := waistCircleHomeomorph_apply F s
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

lemma canonicalWaistDisk_range (F : Family.{u,v}) (s : Waist) :
    Set.range (canonicalWaistDisk F s).map = Metric.closedBall (0:ℂ) 1 :=
  Subtype.range_val

end WP.Critical.PantsCluster
