import Mathlib
/-! A compact nonvanishing family remains nonvanishing on one open parameter
neighborhood. The ordinary Mathlib tube lemma and a compact thickening also
give uniform bounds for its reciprocal and a second continuous family. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma compact_nonzero_parameter_neighborhood (U S T : Set ℂ) (hU : IsOpen U)
    (hS : IsCompact S) (hT : IsCompact T) (hTne : T.Nonempty) (hSU : S⊆U)
    (F : ℂ → ℂ → ℂ) (hF : ∀ z∈U,∀ w : ℂ,ContinuousAt (fun p : ℂ × ℂ => F p.1 p.2) (z,w))
    (hzero : ∀ z∈S,∀ w∈T,F z w≠0) :
    ∃ V : Set ℂ,IsOpen V ∧ S⊆V ∧ IsCompact (closure V) ∧ closure V⊆U ∧
      ∀ z∈closure V,∀ w∈T,F z w≠0 := by
  let G : Set (ℂ × ℂ) := {p | p.1∈U ∧ F p.1 p.2≠0}
  have hG : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually (hU.mem_nhds hp.1),
      (hF p.1 hp.1 p.2).eventually_ne hp.2] with q hqU hqF
    exact ⟨hqU,hqF⟩
  obtain ⟨O,W,hO,hW,hSO,hTW,hOW⟩ := generalized_tube_lemma hS hT hG
    (show S ×ˢ T⊆G from fun p hp => ⟨hSU hp.1,hzero p.1 hp.1 p.2 hp.2⟩)
  have hOU : O⊆U := by
    intro z hz
    obtain ⟨w,hw⟩ := hTne
    exact (hOW (show (z,w)∈O ×ˢ W from ⟨hz,hTW hw⟩)).1
  obtain ⟨δ,hδ,hCδ⟩ := hS.exists_cthickening_subset_open hO hSO
  let V : Set ℂ := Metric.thickening δ S
  have hVC : closure V⊆Metric.cthickening δ S := Metric.closure_thickening_subset_cthickening δ S
  refine ⟨V,Metric.isOpen_thickening,Metric.self_subset_thickening hδ S,
    hS.cthickening.of_isClosed_subset isClosed_closure hVC,(hVC.trans hCδ).trans hOU,?_⟩
  intro z hz w hw
  exact (hOW (show (z,w)∈O ×ˢ W from ⟨hCδ (hVC hz),hTW hw⟩)).2

lemma compact_nonzero_parameter_uniform_bound (U S T : Set ℂ) (hU : IsOpen U)
    (hS : IsCompact S) (hT : IsCompact T) (hTne : T.Nonempty) (hSU : S⊆U)
    (F H : ℂ → ℂ → ℂ)
    (hF : ∀ z∈U,∀ w : ℂ,ContinuousAt (fun p : ℂ × ℂ => F p.1 p.2) (z,w))
    (hH : ∀ z∈U,∀ w : ℂ,ContinuousAt (fun p : ℂ × ℂ => H p.1 p.2) (z,w))
    (hzero : ∀ z∈S,∀ w∈T,F z w≠0) :
    ∃ V : Set ℂ,IsOpen V ∧ S⊆V ∧ IsCompact (closure V) ∧ closure V⊆U ∧
      ∃ M : ℝ,0<M ∧ ∀ z∈closure V,∀ w∈T,F z w≠0 ∧ ‖(F z w)⁻¹‖≤M ∧ ‖H z w‖≤M := by
  obtain ⟨V,hV,hSV,hVC,hVU,hzeroV⟩ := compact_nonzero_parameter_neighborhood U S T hU hS hT hTne hSU F hF hzero
  have hFi : ContinuousOn (fun p : ℂ × ℂ => (F p.1 p.2)⁻¹) (closure V ×ˢ T) := by
    intro p hp
    exact ((hF p.1 (hVU hp.1) p.2).inv₀ (hzeroV p.1 hp.1 p.2 hp.2)).continuousWithinAt
  have hHc : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (closure V ×ˢ T) :=
    fun p hp => (hH p.1 (hVU hp.1) p.2).continuousWithinAt
  obtain ⟨MF,hMF⟩ := (hVC.prod hT).bddAbove_image hFi.norm
  obtain ⟨MH,hMH⟩ := (hVC.prod hT).bddAbove_image hHc.norm
  refine ⟨V,hV,hSV,hVC,hVU,max (max MF MH) 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro z hz w hw
  exact ⟨hzeroV z hz w hw,
    (hMF ⟨(z,w),⟨hz,hw⟩,rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hMH ⟨(z,w),⟨hz,hw⟩,rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))⟩
end WP.Analysis
