import WPFormalization.Critical.PantsClusterJordan
import Mathlib.Analysis.Complex.AbsMax

/-! A plane Jordan disk stays inside any norm bound holding on its actual
boundary. This is the proved Mathlib maximum principle for the identity
function; no extra planar or pants classical field is needed. -/
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.PantsCluster
open Set WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortComplementaryRegionGeometry

lemma boundedDisk_range_compact {f : ClosedLoop ℂ} (D : DiskBoundedBy f) :
    IsCompact (Set.range D.map) := by
  letI : CompactSpace ClosedDisk :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  simpa only [Set.image_univ] using isCompact_univ.image D.map.continuous

lemma boundedDisk_norm_bound {f : ClosedLoop ℂ} (D : DiskBoundedBy f)
    (B : ℝ) (hB : ∀ z ∈ f.trace, ‖z‖ ≤ B) :
    ∀ z ∈ Set.range D.map, ‖z‖ ≤ B := by
  intro z hz
  exact Complex.norm_le_of_forall_mem_frontier_norm_le
    (boundedDisk_range_compact D).isBounded differentiable_id.diffContOnCl
    (fun p hp => hB p (D.frontier_eq ▸ hp)) (subset_closure hz)

lemma boundedDisk_subset_open_unitDisk {f : ClosedLoop ℂ} (D : DiskBoundedBy f)
    (hf : ∀ z ∈ f.trace, ‖z‖ < 1) :
    ∀ z ∈ Set.range D.map, ‖z‖ < 1 := by
  have hcompact : IsCompact f.trace := by
    simpa only [ClosedLoop.trace,Set.image_univ] using isCompact_univ.image f.map.continuous
  have hne : f.trace.Nonempty := Set.range_nonempty _
  obtain ⟨p,hp,hmax⟩ := hcompact.exists_isMaxOn hne continuous_norm.continuousOn
  intro z hz
  exact (boundedDisk_norm_bound D ‖p‖ (fun q hq => hmax hq) z hz).trans_lt (hf p hp)

end WP.Critical.PantsCluster
