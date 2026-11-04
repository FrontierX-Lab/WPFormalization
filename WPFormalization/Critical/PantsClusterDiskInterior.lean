import WPFormalization.Critical.PantsClusterPunctures

/-! Actual punctures enclosed by a canonical primitive Jordan disk are interior
points: none can lie on the actual loop, because its points belong to the
actual twice-punctured disk. No planar classification is assumed. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry Set

lemma boundedDisk_range_isCompact {X : Type*} [MetricSpace X] {f : ClosedLoop X}
    (D : DiskBoundedBy f) : IsCompact (Set.range D.map) := by
  let : CompactSpace ClosedDisk :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) 1)
  simpa only [Set.image_univ] using isCompact_univ.image D.map.continuous

lemma boundedDisk_mem_interior_of_mem_not_trace {X : Type*} [MetricSpace X]
    {f : ClosedLoop X} (D : DiskBoundedBy f) {p : X}
    (hp : p ∈ Set.range D.map) (hpf : p ∉ f.trace) :
    p ∈ interior (Set.range D.map) := by
  by_contra hn
  apply hpf
  rw [←D.frontier_eq]
  exact ⟨subset_closure hp,hn⟩

lemma canonical_puncture_mem_disk_interior (F : Family.{u,v}) (s : Waist)
    (γ : F.Primitive) (D : DiskBoundedBy (planarPrimitiveLoop F s γ))
    {p : ℂ} (hp : p = (1/2:ℂ) ∨ p = -(1/2:ℂ))
    (hD : p ∈ Set.range D.map) : p ∈ interior (Set.range D.map) := by
  apply boundedDisk_mem_interior_of_mem_not_trace D hD
  intro hf
  rcases planarPrimitiveLoop_avoids_punctures F s γ p hf with ⟨hplus,hminus⟩
  exact hp.elim hplus hminus

lemma canonical_nonwaist_JordanDisk_contains_interior_puncture (F : Family.{u,v})
    (s : Waist) (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) (hγ : γ ≠ F.waistClass)
    (D : DiskBoundedBy (planarPrimitiveLoop F s γ)) :
    (1/2:ℂ) ∈ interior (Set.range D.map) ∨
      -(1/2:ℂ) ∈ interior (Set.range D.map) := by
  rcases canonical_nonwaist_JordanDisk_contains_puncture F s BC LS γ hγ D with h | h
  · exact Or.inl (canonical_puncture_mem_disk_interior F s γ D (Or.inl rfl) h)
  · exact Or.inr (canonical_puncture_mem_disk_interior F s γ D (Or.inr rfl) h)

end WP.Critical.PantsCluster
