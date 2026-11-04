import WPFormalization.External.ShortLoopStraighteningGeometry

/-! Elementary topology of actual simple closed loops. Endpoint
identification is handled explicitly; no Jordan theorem is used here. -/
noncomputable section
set_option maxHeartbeats 0
universe x
namespace WP.Critical.PantsCluster
open Set WP.External.ShortLoopStraighteningGeometry

lemma simple_loop_circleMap_injective {X : Type x} [TopologicalSpace X]
    (f : ClosedLoop X) (hf : f.Simple) : Function.Injective f.circleMap := by
  let normalize : unitInterval → unitInterval := fun t => if t=1 then 0 else t
  have hmem (t : unitInterval) : normalize t ∈ Ico (0:unitInterval) 1 := by
    by_cases ht : t=1
    · simp [normalize,ht]
    · simp only [normalize,ite_eq_right ht,Set.mem_Ico]
      exact ⟨t.property.1,lt_of_le_of_ne t.property.2 ht⟩
  have hmap (t : unitInterval) : f.map (normalize t) = f.map t := by
    by_cases ht : t=1
    · simp only [normalize,ht,ite_true]
      exact f.closed
    · simp only [normalize,ite_eq_right ht]
  have hquot (t : unitInterval) :
      (Quot.mk loopCircleEndpoint (normalize t) : LoopCircle) = Quot.mk loopCircleEndpoint t := by
    by_cases ht : t=1
    · simp only [normalize,ht,ite_true]
      exact Quot.sound ⟨rfl,rfl⟩
    · simp only [normalize,ite_eq_right ht]
  intro a b
  refine Quot.inductionOn a (fun s => Quot.inductionOn b (fun t h => ?_))
  change f.map s = f.map t at h
  have hn : normalize s = normalize t :=
    hf (hmem s) (hmem t) ((hmap s).trans (h.trans (hmap t).symm))
  calc
    (Quot.mk loopCircleEndpoint s : LoopCircle) = Quot.mk loopCircleEndpoint (normalize s) := (hquot s).symm
    _ = Quot.mk loopCircleEndpoint (normalize t) := congrArg (Quot.mk loopCircleEndpoint) hn
    _ = Quot.mk loopCircleEndpoint t := hquot t

lemma simple_loop_circleMap_embedding {X : Type x} [TopologicalSpace X] [T2Space X]
    (f : ClosedLoop X) (hf : f.Simple) : Topology.IsClosedEmbedding f.circleMap :=
  f.circleMap.continuous.isClosedEmbedding (simple_loop_circleMap_injective f hf)

def mapClosedLoop {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : C(X,Y)) (f : ClosedLoop X) : ClosedLoop Y where
  map := h.comp f.map
  closed := congrArg h f.closed

lemma mapClosedLoop_circleMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : C(X,Y)) (f : ClosedLoop X) (z : LoopCircle) :
    (mapClosedLoop h f).circleMap z = h (f.circleMap z) := by
  refine Quot.inductionOn z (fun t => ?_)
  rfl

lemma mapClosedLoop_trace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : C(X,Y)) (f : ClosedLoop X) :
    (mapClosedLoop h f).trace = h '' f.trace := by
  exact Set.range_comp h f.map

lemma mapClosedLoop_simple {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : C(X,Y)) (hinj : Function.Injective h) (f : ClosedLoop X) (hf : f.Simple) :
    (mapClosedLoop h f).Simple := by
  intro s hs t ht hst
  exact hf hs ht (hinj hst)

end WP.Critical.PantsCluster
