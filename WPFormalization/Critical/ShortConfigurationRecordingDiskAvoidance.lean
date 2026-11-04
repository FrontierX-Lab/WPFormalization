import WPFormalization.Critical.ShortConfigurationRecordingCutFibers
import WPFormalization.Critical.ShortConfigurationRecordingLoopLength
import WPFormalization.Critical.ShortConfigurationRecordingLoopHomotopy
import WPFormalization.External.ShortComplementaryRegionGeometry
import Mathlib.Analysis.Convex.Contractible
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set WP.External.HyperbolicPacking WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortComplementaryRegionGeometry
open scoped ENNReal

namespace ClosedLoop
variable {X:Type u} [TopologicalSpace X]
def constant (x:X) : WP.External.ShortLoopStraighteningGeometry.ClosedLoop X where
  map:=ContinuousMap.const _ x
  closed:=rfl

lemma contractible_nullhomotopic [ContractibleSpace X]
    (f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X) :
    ∃x,f.FreelyHomotopic (constant x) := by
  obtain ⟨x,⟨h⟩⟩:=id_nullhomotopic X
  refine ⟨x,⟨{toHomotopy:=h.compContinuousMap f.map,prop':=?_}⟩⟩
  intro t
  exact congrArg (fun z=>h (t,z)) f.closed

lemma not_positive_of_nullhomotopic {X:Type u} [MetricSpace X]
    (f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X)
    (h:∃x,f.FreelyHomotopic (constant x)) : ¬f.PositiveHomotopyLength := by
  rintro ⟨ε,hε,hbound⟩
  obtain ⟨x,hx⟩:=h
  have hb:=hbound (constant x) (Or.inl hx)
  have hz:(constant x).length=0:=by simp [WP.External.ShortLoopStraighteningGeometry.ClosedLoop.length,constant,eVariationOn]
  rw [hz] at hb
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hε)) hb
end ClosedLoop

lemma disk_loop_nullhomotopic {X:Type u} [MetricSpace X]
    {f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X}
    (D:DiskBoundedBy f) (l:WP.External.ShortLoopStraighteningGeometry.ClosedLoop X)
    (hsub:l.trace⊆range D.map) : ∃x,l.FreelyHomotopic (ClosedLoop.constant x) := by
  have hex:∀t:unitInterval,∃z:ClosedDisk,D.map z=l.map t:=fun t=>hsub ⟨t,rfl⟩
  choose lift hlift using hex
  have hcont:Continuous lift:=D.embedding.isInducing.continuous_iff.mpr (by
    convert l.map.continuous using 1
    funext t
    exact hlift t)
  let q:WP.External.ShortLoopStraighteningGeometry.ClosedLoop ClosedDisk:={
    map:=⟨lift,hcont⟩
    closed:=D.embedding.injective ((hlift 0).trans (l.closed.trans (hlift 1).symm)) }
  letI:ContractibleSpace ClosedDisk:=(convex_closedBall (0:ℂ) 1).contractibleSpace ⟨0,by simp⟩
  obtain ⟨z,hz⟩:=ClosedLoop.contractible_nullhomotopic q
  refine ⟨D.map z,?_⟩
  have hp:=ClosedLoop.homotopy_postcompose hz D.map
  have hq:ClosedLoop.postcompose q D.map=l := by
    apply ClosedLoop.ext_map
    ext t
    exact hlift t
  rw [hq] at hp
  simpa [ClosedLoop.postcompose,ClosedLoop.constant] using hp

lemma actual_primitive_not_contained_disk (B:BorderedGeometry.{u,v})
    (hcomplete:B.surface.domain=univ) (H:LoopStraighteningClassics B hcomplete)
    {f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point}
    (D:DiskBoundedBy f) (γ:B.curves.Primitive) :
    ¬B.curves.trace γ⊆range D.map := by
  intro hs
  have hc: (primitiveLoop B γ).trace⊆range D.map:=by rw [primitiveLoop_trace];exact hs
  exact ClosedLoop.not_positive_of_nullhomotopic (primitiveLoop B γ)
    (disk_loop_nullhomotopic D (primitiveLoop B γ) hc)
    (primitiveLoop_positiveHomotopyLength B hcomplete H γ)

lemma preconnected_avoids_closed_of_frontier {X:Type u} [TopologicalSpace X]
    (S W:Set X) (hclosed:IsClosed S) (hpre:IsPreconnected W)
    (hnsub:¬W⊆S) (hdisj:Disjoint W (frontier S)) : Disjoint W S := by
  have hsub:W⊆interior S∪Sᶜ := by
    intro p hp
    by_cases hs:p∈S
    · left
      by_contra hnint
      exact (Set.disjoint_left.mp hdisj) hp ⟨subset_closure hs,hnint⟩
    · exact Or.inr hs
  have hor:=hpre.subset_or_subset isOpen_interior hclosed.isOpen_compl
    (Set.disjoint_left.mpr (fun p hp hn=>hn (interior_subset hp))) hsub
  rcases hor with hi|ho
  · exact (hnsub (hi.trans interior_subset)).elim
  · exact Set.disjoint_left.mpr (fun p hp hs=>ho hp hs)

lemma actual_primitive_disjoint_disk (B:BorderedGeometry.{u,v})
    (hcomplete:B.surface.domain=univ) (H:LoopStraighteningClassics B hcomplete)
    {f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point}
    (D:DiskBoundedBy f) (γ:B.curves.Primitive)
    (hboundary:Disjoint (B.curves.trace γ) f.trace) :
    Disjoint (B.curves.trace γ) (range D.map) := by
  letI:CompactSpace ClosedDisk:=isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) 1)
  apply preconnected_avoids_closed_of_frontier (range D.map) (B.curves.trace γ)
    (isCompact_range D.map.continuous).isClosed (primitive_trace_preconnected B γ)
    (actual_primitive_not_contained_disk B hcomplete H D γ)
  rwa [D.frontier_eq]

end WP.Critical.ShortConfiguration
