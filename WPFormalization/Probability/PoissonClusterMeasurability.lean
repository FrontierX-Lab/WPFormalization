import WPFormalization.Probability.PoissonClusterCompactParents
import WPFormalization.External.PointProcessProbability
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Function.Floor
noncomputable section
set_option maxHeartbeats 0
universe u
namespace WP.Probability.PoissonCluster
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Classical

lemma pointMeasure_eval_measurable (S : Set ℝ≥0) (hS : MeasurableSet S)
    (hc : IsCompact (closure S)) :
    Measurable (fun ξ : PointMeasure ℝ≥0 => ξ.toMeasure S) := by
  let W : RelCompactBorelWindow ℝ≥0 := ⟨S,hS,hc⟩
  have h := (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
    (WP.External.pointMeasure_count_measurable ℝ≥0 W)
  have he : (fun ξ : PointMeasure ℝ≥0 => ξ.toMeasure S)=
      fun ξ => (ξ.count ℝ≥0 W : ℝ≥0∞) :=
    funext (fun ξ => PointMeasure.count_spec ℝ≥0 ξ W)
  rw [he]
  exact h

/- Counting measure has no nonempty null sets, so the existing generic
AE prefix generator also gives the ordinary Borel prefix generator. -/
lemma pointMeasure_measurable_of_prefix_counts {Ω : Type*} [MeasurableSpace Ω]
    (Ξ : Ω → PointMeasure ℝ≥0)
    (h : ∀b : ℝ≥0,Measurable (fun ω => (Ξ ω).count ℝ≥0 (nnrealPrefixWindow b))) :
    Measurable Ξ := by
  have ha := WP.External.pointMeasure_nnreal_aemeasurable_of_prefix_counts
    (Measure.count : Measure Ω) Ξ (fun b => (h b).aemeasurable)
  have he : Ξ=ha.mk Ξ := funext (Measure.ae_count_iff.mp ha.ae_eq_mk)
  rw [he]
  exact ha.measurable_mk

lemma measurable_pointMeasure_prefix_count {Ω : Type*} [MeasurableSpace Ω]
    (Ξ : Ω → PointMeasure ℝ≥0) (b : ℝ≥0)
    (h : Measurable (fun ω => (Ξ ω).toMeasure (Iic b))) :
    Measurable (fun ω => (Ξ ω).count ℝ≥0 (nnrealPrefixWindow b)) := by
  have hm := h.ennreal_toReal.nat_floor
  have he : (fun ω => ⌊((Ξ ω).toMeasure (Iic b)).toReal⌋₊)=
      fun ω => (Ξ ω).count ℝ≥0 (nnrealPrefixWindow b) := by
    funext ω
    rw [show (Iic b : Set ℝ≥0)=(nnrealPrefixWindow b).carrier from rfl,
      PointMeasure.count_spec]
    simp
  rwa [he] at hm

variable {J : Type u} [Countable J]

lemma indexedClusterPointMeasure_measurable (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ))
    (hbound : ∀L : ℝ≥0,∃C : ℝ≥0∞,C<∞ ∧
      ∀s : ℝ≥0,0<s→indexedKernelMeasure length s (Iic L)≤C)
    (hproper : ∀(L s : ℝ≥0),2*L<s→indexedKernelMeasure length s (Iic L)=0) :
    Measurable (fun ξ : PointMeasure ℝ≥0 => indexedClusterPointMeasure length hlength ξ hbound hproper) := by
  apply pointMeasure_measurable_of_prefix_counts
  intro b
  apply measurable_pointMeasure_prefix_count
  have hterm (γ : J) : Measurable (fun ξ : PointMeasure ℝ≥0 =>
      ((ξ.toMeasure.restrict (Ioi (0:ℝ≥0))).map (length γ)) (Iic b)) := by
    let S : Set ℝ≥0 := (length γ) ⁻¹' Iic b ∩ Ioi (0:ℝ≥0)
    have hS : MeasurableSet S := (measurableSet_Iic.preimage (hlength γ)).inter measurableSet_Ioi
    have hsub : S ⊆ Iic (2*b) := by
      intro s hs
      by_contra hnot
      have hz := hproper b s (lt_of_not_ge hnot)
      exact ((indexedKernelMeasure_eq_zero_iff length s _ measurableSet_Iic).mp hz γ) hs.1
    have hc : IsCompact (closure S) := (isCompact_nnreal_prefix (2*b)).of_isClosed_subset
      isClosed_closure (closure_minimal hsub isClosed_Iic)
    have he (ξ : PointMeasure ℝ≥0) :
        ((ξ.toMeasure.restrict (Ioi (0:ℝ≥0))).map (length γ)) (Iic b)=ξ.toMeasure S := by
      rw [Measure.map_apply (hlength γ) measurableSet_Iic,
        Measure.restrict_apply (measurableSet_Iic.preimage (hlength γ))]
    simp_rw [he]
    exact pointMeasure_eval_measurable S hS hc
  have hm := Measurable.ennreal_tsum hterm
  simpa only [indexedClusterPointMeasure,indexedClusterMeasure,
    Measure.sum_apply _ measurableSet_Iic] using hm

lemma compactParentClusterPointMeasure_measurable (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ)) (W : RelCompactBorelWindow ℝ≥0)
    (hbound : ∀L : ℝ≥0,∃C : ℝ≥0∞,C<∞ ∧
      ∀s : ℝ≥0,0<s→indexedKernelMeasure length s (Iic L)≤C) :
    Measurable (fun ξ : PointMeasure ℝ≥0 => compactParentClusterPointMeasure length hlength ξ W hbound) := by
  apply pointMeasure_measurable_of_prefix_counts
  intro b
  apply measurable_pointMeasure_prefix_count
  have hterm (γ : J) : Measurable (fun ξ : PointMeasure ℝ≥0 =>
      (((ξ.toMeasure.restrict W.carrier).restrict (Ioi (0:ℝ≥0))).map (length γ)) (Iic b)) := by
    let S : Set ℝ≥0 := ((length γ) ⁻¹' Iic b ∩ Ioi (0:ℝ≥0)) ∩ W.carrier
    have hS : MeasurableSet S :=
      ((measurableSet_Iic.preimage (hlength γ)).inter measurableSet_Ioi).inter W.measurableSet
    have hc : IsCompact (closure S) := W.compactClosure.of_isClosed_subset isClosed_closure
      (closure_mono (by intro s hs;exact hs.2))
    have he (ξ : PointMeasure ℝ≥0) :
        (((ξ.toMeasure.restrict W.carrier).restrict (Ioi (0:ℝ≥0))).map (length γ)) (Iic b)=ξ.toMeasure S := by
      rw [Measure.map_apply (hlength γ) measurableSet_Iic,
        Measure.restrict_apply (measurableSet_Iic.preimage (hlength γ)),
        Measure.restrict_apply ((measurableSet_Iic.preimage (hlength γ)).inter measurableSet_Ioi)]
    simp_rw [he]
    exact pointMeasure_eval_measurable S hS hc
  have hm := Measurable.ennreal_tsum hterm
  simpa only [compactParentClusterPointMeasure,indexedClusterMeasure,
    Measure.sum_apply _ measurableSet_Iic] using hm

end WP.Probability.PoissonCluster
