import WPFormalization.Probability.PointMeasureDilationSlutsky
import WPFormalization.External.PointMeasureDilationTopology
import Mathlib.Topology.Metrizable.Uniformity

/-! The actual positive measure-map dilation preserves the limiting point
process law when its positive scale tends to one in probability. All changing
spaces/measures and eventual probability/measurability are explicit. The only
new classical inputs are the separately registered pure vague-topology facts;
no geometric or random-scale limit is assumed as a field. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Set Filter
open scoped ENNReal Topology

lemma positiveScale_dist_one (a : PositiveScale) :
    dist a (⟨1,by norm_num⟩ : PositiveScale)=|((a.val):ℝ)-1| := rfl

lemma aemeasurable_pointMeasureDilation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ξ : Ω → PointMeasure NNReal) (a : Ω → PositiveScale)
    (hΞ : AEMeasurable Ξ μ) (ha : AEMeasurable a μ) :
    AEMeasurable (fun ω => pointMeasureDilation (a ω) (Ξ ω)) μ :=
  External.pointMeasure_nnreal_dilation_joint_continuous.measurable.comp_aemeasurable
    (ha.prodMk hΞ)

lemma lawConverges_pointMeasureDilation {Ω : ℕ → Type*} [∀j,MeasurableSpace (Ω j)]
    {Ωlimit : Type*} [MeasurableSpace Ωlimit]
    (μ : (j : ℕ) → Measure (Ω j))
    (Ξ : (j : ℕ) → Ω j → PointMeasure NNReal)
    (a : (j : ℕ) → Ω j → PositiveScale)
    (Q : Measure Ωlimit) [IsProbabilityMeasure Q] (Z : Ωlimit → PointMeasure NNReal)
    (hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hΞ : ∀ᶠj in atTop,AEMeasurable (Ξ j) (μ j))
    (ha : ∀ᶠj in atTop,AEMeasurable (a j) (μ j))
    (hZ : AEMeasurable Z Q) (hLaw : LawConverges μ Ξ Q Z)
    (hconv : ∀δ>0,Tendsto (fun j => (μ j) {ω | δ≤|(((a j ω).val):ℝ)-1|}) atTop (𝓝 0)) :
    LawConverges μ (fun j ω => pointMeasureDilation (a j ω) (Ξ j ω)) Q Z := by
  let : TopologicalSpace.MetrizableSpace (PointMeasure NNReal) :=
    External.pointMeasure_nnreal_vague_metrizable_secondCountable.1
  let : SecondCountableTopology (PointMeasure NNReal) :=
    External.pointMeasure_nnreal_vague_metrizable_secondCountable.2
  letI : MetricSpace (PointMeasure NNReal) :=
    TopologicalSpace.metrizableSpaceMetric (PointMeasure NNReal)
  let one : PositiveScale := ⟨1,by norm_num⟩
  have htail : ∀δ>0,Tendsto (fun j => (μ j).real {ω | δ≤dist (a j ω) one}) atTop (𝓝 0) := by
    intro δ hδ
    have he := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp (hconv δ hδ)
    simpa only [Function.comp_def,ENNReal.toReal_zero,measureReal_def,positiveScale_dist_one,one] using he
  have hp := lawConverges_prodMk_const_eventually μ Ξ a Q Z one hprob hΞ ha hZ hLaw htail
  have hc : Continuous (fun p : PointMeasure NNReal × PositiveScale => pointMeasureDilation p.2 p.1) :=
    External.pointMeasure_nnreal_dilation_joint_continuous.comp continuous_swap
  have he := lawConverges_continuous_comp μ (fun j ω => (Ξ j ω,a j ω)) Q
    (fun ω => (Z ω,one)) (fun p => pointMeasureDilation p.2 p.1) hc hp
  simpa only [one,pointMeasureDilation_one] using he

end WP.Probability
