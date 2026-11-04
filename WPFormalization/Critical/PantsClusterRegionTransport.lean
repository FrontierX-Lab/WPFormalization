import WPFormalization.Critical.PantsClusterDiskInterior

/-! Transport actual peripheral-end regions through open charts. All closed
image hypotheses are explicit topological conditions; no classification of
pants curves, filling, or length support is postulated. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace WP.Critical.PantsCluster
open Set WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortComplementaryRegionGeometry

lemma openEmbedding_image_frontier_of_closed_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {h : X → Y} (hh : Topology.IsOpenEmbedding h) (A : Set X)
    (hc : IsClosed (h '' A)) : frontier (h '' A) = h '' frontier A := by
  have he : h ⁻¹' frontier (h '' A) = frontier A := by
    rw [hh.isOpenMap.preimage_frontier_eq_frontier_preimage hh.continuous,
      hh.injective.preimage_image]
  ext p
  constructor
  · intro hp
    obtain ⟨x,hx,rfl⟩ := hc.closure_subset (frontier_subset_closure hp)
    exact ⟨x,he ▸ hp,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact show x ∈ h ⁻¹' frontier (h '' A) from he.symm ▸ hx

def cuspEnd_liftOpen {X : Type*} [MetricSpace X]
    (U : Set X) (hU : IsOpen U) {f : ClosedLoop X} (E : CuspEndBoundedBy f)
    (hf : ∀ t, f.map t ∈ U) (hE : ∀ z, E.map z ∈ U) :
    CuspEndBoundedBy (subtypeClosedLoop U f hf) := by
  let map : C(LoopCircle × Ici (0:ℝ),U) :=
    ⟨fun z => ⟨E.map z,hE z⟩,E.map.continuous.subtype_mk _⟩
  have hinner : map '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val} =
      Subtype.val ⁻¹' (E.map '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val}) := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z,hz,rfl⟩
    · rintro ⟨z,hz,hzp⟩
      exact ⟨z,hz,Subtype.ext hzp⟩
  have hrange : Set.range map = Subtype.val ⁻¹' Set.range E.map := by
    ext p
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z,rfl⟩
    · rintro ⟨z,hzp⟩
      exact ⟨z,Subtype.ext hzp⟩
  refine {
    map := map
    closedEmbedding := ⟨?_,?_⟩
    boundary := ?_
    inner_open := ?_
    frontier_eq := ?_ }
  · exact (Topology.IsEmbedding.of_comp_iff (f := map)
      (g := (Subtype.val : U → X)) .subtypeVal).mp E.closedEmbedding.isEmbedding
  · rw [hrange]
    exact E.closedEmbedding.isClosed_range.preimage continuous_subtype_val
  · intro z
    apply Subtype.ext
    change E.map _ = ((subtypeClosedLoop U f hf).circleMap z).val
    rw [subtypeClosedLoop_circleMap,E.boundary]
  · rw [hinner]
    exact E.inner_open.preimage continuous_subtype_val
  · rw [hrange,←hU.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val,E.frontier_eq,subtypeClosedLoop_trace]

def cuspEnd_mapOpenEmbedding {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (h : C(X,Y)) (hh : Topology.IsOpenEmbedding h) {f : ClosedLoop X}
    (E : CuspEndBoundedBy f) (hc : IsClosed (h '' Set.range E.map)) :
    CuspEndBoundedBy (mapClosedLoop h f) where
  map := h.comp E.map
  closedEmbedding := ⟨hh.isEmbedding.comp E.closedEmbedding.isEmbedding,by
    change IsClosed (Set.range (h ∘ E.map))
    simpa only [Set.range_comp] using hc⟩
  boundary := by
    intro z
    change h (E.map _) = _
    rw [E.boundary,mapClosedLoop_circleMap]
  inner_open := by
    rw [ContinuousMap.coe_comp,Set.image_comp]
    exact hh.isOpenMap _ E.inner_open
  frontier_eq := by
    change frontier (Set.range (h ∘ E.map)) = _
    rw [Set.range_comp,openEmbedding_image_frontier_of_closed_image hh _ hc,E.frontier_eq]
    exact (mapClosedLoop_trace h f).symm

end WP.Critical.PantsCluster
