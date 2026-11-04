import WPFormalization.Critical.PantsClusterGenericSimple
import Mathlib.Analysis.Normed.Module.Connected

/-! Actual two-punctured closed disk connectedness is local Mathlib topology:
radially clip the path-connected complement of two plane points. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open Set WP.External.PantsCluster WP.External.HyperbolicPacking

def radialClip (z : ℂ) : ℂ := (max 1 ‖z‖)⁻¹ • z

lemma radialClip_continuous : Continuous radialClip := by
  have hc : Continuous (fun z : ℂ => max (1:ℝ) ‖z‖) := continuous_const.max continuous_norm
  have hi := hc.inv₀ (fun z => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖z‖)))
  exact hi.smul continuous_id

lemma radialClip_eq_self {z : ℂ} (hz : ‖z‖ ≤ 1) : radialClip z = z := by
  simp only [radialClip,max_eq_left hz,inv_one,one_smul]

lemma radialClip_norm_eq_one {z : ℂ} (hz : 1 ≤ ‖z‖) : ‖radialClip z‖ = 1 := by
  have hp : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz
  rw [radialClip,norm_smul,Real.norm_eq_abs,max_eq_right hz,abs_of_pos (inv_pos.mpr hp)]
  exact inv_mul_cancel₀ hp.ne'

lemma radialClip_norm_le (z : ℂ) : ‖radialClip z‖ ≤ 1 := by
  by_cases hz : ‖z‖ ≤ 1
  · rwa [radialClip_eq_self hz]
  · exact (radialClip_norm_eq_one (le_of_not_ge hz)).le

lemma radialClip_avoids {z p : ℂ} (hp : ‖p‖ < 1) (hz : z ≠ p) : radialClip z ≠ p := by
  by_cases hn : ‖z‖ ≤ 1
  · rwa [radialClip_eq_self hn]
  · intro he
    have := radialClip_norm_eq_one (z := z) (le_of_not_ge hn)
    rw [he] at this
    exact hp.ne this

lemma twicePuncturedDisk_pathConnectedSpace : PathConnectedSpace TwicePuncturedDisk := by
  let S : Set ℂ := {(1/2:ℂ),-(1/2:ℂ)}
  have hcount : S.Countable := ((Set.finite_singleton (-(1/2:ℂ))).insert (1/2:ℂ)).countable
  have hconn : IsPathConnected Sᶜ := hcount.isPathConnected_compl_of_one_lt_rank (by
    rw [Complex.rank_real_complex]
    norm_num)
  letI : PathConnectedSpace ↥(Sᶜ) := isPathConnected_iff_pathConnectedSpace.mp hconn
  let f : C(↥(Sᶜ),TwicePuncturedDisk) := ⟨fun z => ⟨radialClip z.val,radialClip_norm_le _,by
    have hz : z.val ≠ (1/2:ℂ) ∧ z.val ≠ -(1/2:ℂ) := by
      simpa only [S,Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using z.property
    exact ⟨radialClip_avoids (by norm_num) hz.1,radialClip_avoids (by norm_num) hz.2⟩⟩,
    (radialClip_continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hsurj : Function.Surjective f := by
    intro z
    let w : ↥(Sᶜ) := ⟨z.val,by
      simpa only [S,Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
        using z.property.2⟩
    refine ⟨w,?_⟩
    apply Subtype.ext
    exact radialClip_eq_self z.property.1
  apply pathConnectedSpace_iff_univ.mpr
  rw [←hsurj.range_eq]
  exact isPathConnected_range f.continuous

lemma actual_pants_pathConnectedSpace (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) : PathConnectedSpace B.surface.Point := by
  letI := twicePuncturedDisk_pathConnectedSpace
  obtain ⟨e,he⟩ := hp
  exact e.symm.pathConnectedSpace

lemma actual_pants_preconnectedSpace (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) : PreconnectedSpace B.surface.Point := by
  letI := actual_pants_pathConnectedSpace B hp
  infer_instance

end WP.Critical.PantsCluster
