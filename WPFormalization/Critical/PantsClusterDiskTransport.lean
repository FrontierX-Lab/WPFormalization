import WPFormalization.Critical.PantsClusterJordanBounds

/-! Transport actual bounded disks under open embeddings. This will allow
the Jordan disk inside an open puncture-free pants chart to be regarded as
an actual intrinsic disk; no curve or filling classification is an input. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace WP.Critical.PantsCluster
open Set WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortComplementaryRegionGeometry

lemma openEmbedding_image_frontier_of_compact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {h : X → Y} (hh : Topology.IsOpenEmbedding h) (A : Set X) (hA : IsCompact A) :
    frontier (h '' A) = h '' frontier A := by
  have he : h ⁻¹' frontier (h '' A) = frontier A := by
    rw [hh.isOpenMap.preimage_frontier_eq_frontier_preimage hh.continuous,
      hh.injective.preimage_image]
  have hc : IsClosed (h '' A) := (hA.image hh.continuous).isClosed
  ext p
  constructor
  · intro hp
    obtain ⟨x,hx,rfl⟩ := hc.closure_subset (frontier_subset_closure hp)
    exact ⟨x,he ▸ hp,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact show x ∈ h ⁻¹' frontier (h '' A) from he.symm ▸ hx

def boundedDisk_mapOpenEmbedding {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (h : C(X,Y)) (hh : Topology.IsOpenEmbedding h) {f : ClosedLoop X}
    (D : DiskBoundedBy f) : DiskBoundedBy (mapClosedLoop h f) where
  map := h.comp D.map
  embedding := hh.isEmbedding.comp D.embedding
  circle := D.circle
  boundary := by
    intro z
    change h (D.map _) = _
    rw [D.boundary,mapClosedLoop_circleMap]
  inner_open := by
    rw [ContinuousMap.coe_comp,Set.image_comp]
    exact hh.isOpenMap _ D.inner_open
  frontier_eq := by
    have hcompact : IsCompact (Set.range D.map) := by
      letI : CompactSpace ClosedDisk := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) 1)
      simpa only [Set.image_univ] using isCompact_univ.image D.map.continuous
    change frontier (Set.range (h ∘ D.map)) = _
    rw [Set.range_comp,openEmbedding_image_frontier_of_compact hh _ hcompact,D.frontier_eq]
    exact (mapClosedLoop_trace h f).symm

def subtypeClosedLoop {X : Type*} [TopologicalSpace X] (U : Set X)
    (f : ClosedLoop X) (hf : ∀ t, f.map t ∈ U) : ClosedLoop U where
  map := ⟨fun t => ⟨f.map t,hf t⟩,f.map.continuous.subtype_mk _⟩
  closed := Subtype.ext f.closed

lemma subtypeClosedLoop_circleMap {X : Type*} [TopologicalSpace X] (U : Set X)
    (f : ClosedLoop X) (hf : ∀ t, f.map t ∈ U) (z : LoopCircle) :
    ((subtypeClosedLoop U f hf).circleMap z).val = f.circleMap z := by
  refine Quot.inductionOn z (fun t => ?_)
  rfl

lemma subtypeClosedLoop_trace {X : Type*} [TopologicalSpace X] (U : Set X)
    (f : ClosedLoop X) (hf : ∀ t, f.map t ∈ U) :
    (subtypeClosedLoop U f hf).trace = Subtype.val ⁻¹' f.trace := by
  ext p
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩
  · rintro ⟨t,ht⟩
    exact ⟨t,Subtype.ext ht⟩

def boundedDisk_liftOpen {X : Type*} [MetricSpace X]
    (U : Set X) (hU : IsOpen U) {f : ClosedLoop X} (D : DiskBoundedBy f)
    (hf : ∀ t, f.map t ∈ U) (hD : ∀ z, D.map z ∈ U) :
    DiskBoundedBy (subtypeClosedLoop U f hf) := by
  let map : C(ClosedDisk,U) :=
    ⟨fun z => ⟨D.map z,hD z⟩,D.map.continuous.subtype_mk _⟩
  have hinner : map '' {z : ClosedDisk | dist z.val 0 < 1} =
      Subtype.val ⁻¹' (D.map '' {z : ClosedDisk | dist z.val 0 < 1}) := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z,hz,rfl⟩
    · rintro ⟨z,hz,hzp⟩
      exact ⟨z,hz,Subtype.ext hzp⟩
  have hrange : Set.range map = Subtype.val ⁻¹' Set.range D.map := by
    ext p
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z,rfl⟩
    · rintro ⟨z,hzp⟩
      exact ⟨z,Subtype.ext hzp⟩
  refine {
    map := map
    embedding := ?_
    circle := D.circle
    boundary := ?_
    inner_open := ?_
    frontier_eq := ?_ }
  · exact (Topology.IsEmbedding.of_comp_iff (f := map)
      (g := (Subtype.val : U → X)) .subtypeVal).mp D.embedding
  · intro z
    apply Subtype.ext
    change D.map _ = ((subtypeClosedLoop U f hf).circleMap z).val
    rw [subtypeClosedLoop_circleMap,D.boundary]
  · rw [hinner]
    exact D.inner_open.preimage continuous_subtype_val
  · rw [hrange,←hU.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val,D.frontier_eq,subtypeClosedLoop_trace]

end WP.Critical.PantsCluster
