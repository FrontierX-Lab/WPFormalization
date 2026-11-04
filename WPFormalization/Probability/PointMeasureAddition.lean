import WPFormalization.Probability.TwoColorPointMeasuresTopology
noncomputable section
namespace WP.Probability
open MeasureTheory Set
open scoped ENNReal NNReal Topology CompactlySupported

lemma pointMeasure_add_locallyFinite (ξ η : PointMeasure ℝ≥0) :
    IsLocallyFiniteMeasure (ξ.toMeasure+η.toMeasure) := by
  constructor
  intro x
  refine ⟨Iic (x+1),Iic_mem_nhds (by simp),?_⟩
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.mpr ⟨window_measure_lt_top ℝ≥0 ξ.toMeasure (nnrealPrefixWindow (x+1)),
    window_measure_lt_top ℝ≥0 η.toMeasure (nnrealPrefixWindow (x+1))⟩

def pointMeasureAdd (ξ η : PointMeasure ℝ≥0) : PointMeasure ℝ≥0 where
  toMeasure := ξ.toMeasure + η.toMeasure
  locallyFinite := pointMeasure_add_locallyFinite ξ η
  regular := by
    letI := pointMeasure_add_locallyFinite ξ η
    infer_instance
  integerOnRelCompact := by
    intro B hB hc
    obtain ⟨m,hm⟩ := ξ.integerOnRelCompact B hB hc
    obtain ⟨n,hn⟩ := η.integerOnRelCompact B hB hc
    refine ⟨m+n,?_⟩
    simp only [Measure.add_apply,hm,hn,Nat.cast_add]

lemma pointMeasureAdd_toMeasure (ξ η : PointMeasure ℝ≥0) :
    (pointMeasureAdd ξ η).toMeasure=ξ.toMeasure+η.toMeasure := rfl

lemma pointMeasureAdd_integral (ξ η : PointMeasure ℝ≥0) (f : C_c(ℝ≥0,ℝ)) :
    (∫x,f x ∂(pointMeasureAdd ξ η).toMeasure)=
      (∫x,f x ∂ξ.toMeasure)+(∫x,f x ∂η.toMeasure) :=
  integral_add_measure f.integrable f.integrable

lemma pointMeasureAdd_continuous :
    Continuous (fun p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0 => pointMeasureAdd p.1 p.2) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  simpa only [Function.comp_def,pointMeasureAdd_integral,Pi.add_def] using
    ((pointMeasure_vague_test_continuous f).comp continuous_fst).add
      ((pointMeasure_vague_test_continuous f).comp continuous_snd)

end WP.Probability
