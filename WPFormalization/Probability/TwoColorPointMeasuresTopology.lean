import WPFormalization.Probability.TwoColorPointMeasures

/-! The direct-sum encoding respects the actual compact-test vague topology. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace WP.Probability
open MeasureTheory Filter Set Topology
open scoped Topology CompactlySupported ENNReal NNReal

private def colorInl : CocompactMap ℝ≥0 TwoColorSpace where
  toFun := Sum.inl
  continuous_toFun := continuous_inl
  cocompact_tendsto' := IsClosedEmbedding.inl.tendsto_cocompact

private def colorInr : CocompactMap ℝ≥0 TwoColorSpace where
  toFun := Sum.inr
  continuous_toFun := continuous_inr
  cocompact_tendsto' := IsClosedEmbedding.inr.tendsto_cocompact

/-- Restriction of a compactly supported test to either clopen color. -/
def twoColorTestLeft (f : C_c(TwoColorSpace,ℝ)) : C_c(ℝ≥0,ℝ) := f.comp colorInl

def twoColorTestRight (f : C_c(TwoColorSpace,ℝ)) : C_c(ℝ≥0,ℝ) := f.comp colorInr

lemma twoColorEncode_integral (ξ : TwoColorPointMeasure) (f : C_c(TwoColorSpace,ℝ)) :
    (∫ z,f z ∂(twoColorEncode ξ).toMeasure) =
      (∫ x,twoColorTestLeft f x ∂ξ.1.toMeasure) +
        ∫ x,twoColorTestRight f x ∂ξ.2.toMeasure := by
  have hl : Integrable f (Measure.map Sum.inl ξ.1.toMeasure) :=
    (integrable_map_measure f.continuous.aestronglyMeasurable measurable_inl.aemeasurable).mpr
      (twoColorTestLeft f).integrable
  have hr : Integrable f (Measure.map Sum.inr ξ.2.toMeasure) :=
    (integrable_map_measure f.continuous.aestronglyMeasurable measurable_inr.aemeasurable).mpr
      (twoColorTestRight f).integrable
  change (∫ z,f z ∂(Measure.map Sum.inl ξ.1.toMeasure + Measure.map Sum.inr ξ.2.toMeasure))=_
  rw [integral_add_measure hl hr]
  congr 1
  · exact integral_map measurable_inl.aemeasurable f.continuous.aestronglyMeasurable
  · exact integral_map measurable_inr.aemeasurable f.continuous.aestronglyMeasurable

/-- Each compact-test integral is continuous by the actual definition of
vague topology, independent of any convergence criterion. -/
lemma pointMeasure_vague_test_continuous {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] (f : C_c(E,ℝ)) :
    Continuous (fun ξ : PointMeasure E => ∫ x,f x ∂ξ.toMeasure) :=
  by
    have h : Continuous (fun ξ : PointMeasure E => fun h : C_c(E,ℝ) => ∫ x,h x ∂ξ.toMeasure) :=
      continuous_induced_dom
    exact (continuous_apply f).comp h

lemma twoColorEncode_continuous : Continuous twoColorEncode := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  have hleft : Continuous (fun ξ : TwoColorPointMeasure => ∫ x,twoColorTestLeft f x ∂ξ.1.toMeasure) :=
    (pointMeasure_vague_test_continuous (twoColorTestLeft f)).comp continuous_fst
  have hright : Continuous (fun ξ : TwoColorPointMeasure => ∫ x,twoColorTestRight f x ∂ξ.2.toMeasure) :=
    (pointMeasure_vague_test_continuous (twoColorTestRight f)).comp continuous_snd
  simpa only [Function.comp_def,twoColorEncode_integral,Pi.add_def] using hleft.add hright

end WP.Probability
