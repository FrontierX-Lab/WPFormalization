import WPFormalization.Probability.TwoColorPointMeasuresTopology
import Mathlib.Topology.Algebra.GroupWithZero
/-! Actual positive dilation of locally finite Radon point measures on the
nonnegative half-line. The object is the ordinary measure pushforward; all
preservation properties and fixed-scale continuity below are proved locally.
Joint continuity and countable metrization are separate classical inputs. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Set
open scoped ENNReal NNReal Topology CompactlySupported

def pointMeasureHomeomorphMap (e : ℝ≥0 ≃ₜ ℝ≥0) (ξ : PointMeasure ℝ≥0) :
    PointMeasure ℝ≥0 where
  toMeasure := ξ.toMeasure.map e
  locallyFinite := by
    constructor
    intro x
    obtain ⟨U,hU,hfin⟩ := ξ.locallyFinite.finiteAtNhds (e.symm x)
    refine ⟨e.symm ⁻¹' U,e.symm.continuous.continuousAt hU,?_⟩
    rw [e.measurableEmbedding.map_apply]
    have he : e ⁻¹' (e.symm ⁻¹' U)=U := by ext z; simp
    rw [he]
    exact hfin
  regular := by
    have hl : IsLocallyFiniteMeasure (ξ.toMeasure.map e) := by
      constructor
      intro x
      obtain ⟨U,hU,hfin⟩ := ξ.locallyFinite.finiteAtNhds (e.symm x)
      refine ⟨e.symm ⁻¹' U,e.symm.continuous.continuousAt hU,?_⟩
      rw [e.measurableEmbedding.map_apply]
      have he : e ⁻¹' (e.symm ⁻¹' U)=U := by ext z; simp
      rw [he]
      exact hfin
    let := hl
    infer_instance
  integerOnRelCompact := by
    intro B hB hc
    rw [e.measurableEmbedding.map_apply]
    apply ξ.integerOnRelCompact _ (hB.preimage e.continuous.measurable)
    rw [←e.preimage_closure]
    exact e.isCompact_preimage.mpr hc

/-- Actual positive scaling parameter, with its inherited ordinary topology. -/
abbrev PositiveScale := {a : ℝ≥0 // 0<a}

def pointMeasureDilation (a : PositiveScale) (ξ : PointMeasure ℝ≥0) :
    PointMeasure ℝ≥0 := pointMeasureHomeomorphMap (Homeomorph.mulLeft₀ a.val a.property.ne') ξ

lemma pointMeasureDilation_toMeasure (a : PositiveScale) (ξ : PointMeasure ℝ≥0) :
    (pointMeasureDilation a ξ).toMeasure=ξ.toMeasure.map (fun x => a.val*x) := rfl

lemma pointMeasure_ext_toMeasure {ξ η : PointMeasure ℝ≥0}
    (h : ξ.toMeasure=η.toMeasure) : ξ=η := by
  cases ξ
  cases η
  cases h
  rfl

lemma pointMeasureDilation_one (ξ : PointMeasure ℝ≥0) :
    pointMeasureDilation ⟨1,by norm_num⟩ ξ=ξ := by
  apply pointMeasure_ext_toMeasure
  rw [pointMeasureDilation_toMeasure]
  simpa only [one_mul] using (Measure.map_id' (μ:=ξ.toMeasure))

lemma pointMeasureHomeomorphMap_integral (e : ℝ≥0 ≃ₜ ℝ≥0)
    (ξ : PointMeasure ℝ≥0) (f : C_c(ℝ≥0,ℝ)) :
    (∫ x,f x ∂(pointMeasureHomeomorphMap e ξ).toMeasure)=
      ∫ x,(f.comp e.toCocompactMap) x ∂ξ.toMeasure := by
  exact integral_map e.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable

lemma pointMeasureHomeomorphMap_continuous (e : ℝ≥0 ≃ₜ ℝ≥0) :
    Continuous (pointMeasureHomeomorphMap e) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  simp only [Function.comp_def,pointMeasureHomeomorphMap_integral]
  exact pointMeasure_vague_test_continuous (f.comp e.toCocompactMap)

lemma pointMeasureDilation_continuous_fixed (a : PositiveScale) :
    Continuous (pointMeasureDilation a) :=
  pointMeasureHomeomorphMap_continuous _

end WP.Probability
