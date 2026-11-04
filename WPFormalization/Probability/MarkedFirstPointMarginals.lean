import WPFormalization.Probability.MarkedFirstPointDefinitions
noncomputable section
namespace WP.Probability
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

def markedFirstTimeMeasure (ν:Measure ℝ≥0) (η:Measure ℕ) : Measure ℝ≥0 :=
  ν.withDensity (fun t=>ENNReal.ofReal
    (Real.exp (-((η univ).toReal*(ν (Iic t)).toReal))))

lemma markedFirstArrivalStateMeasure_univ (ν:Measure ℝ≥0) (η:Measure ℕ) [IsFiniteMeasure η] :
    markedFirstArrivalStateMeasure ν η univ=
      markedFirstTimeMeasure ν η univ * η univ := by
  rw [markedFirstArrivalStateMeasure,Measure.map_apply markedFirstEmbed_measurable MeasurableSet.univ]
  rw [preimage_univ]
  change ((markedFirstTimeMeasure ν η).prod η) univ=_
  rw [←univ_prod_univ,Measure.prod_prod]

lemma markedFirstTimeMeasure_mass (ν:Measure ℝ≥0) (η:Measure ℕ) [IsFiniteMeasure η]
    [IsProbabilityMeasure (markedFirstArrivalStateMeasure ν η)] :
    markedFirstTimeMeasure ν η univ=(η univ)⁻¹ := by
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [←markedFirstArrivalStateMeasure_univ,measure_univ]

lemma markedFirstArrivalStateMeasure_mark_marginal (ν:Measure ℝ≥0) (η:Measure ℕ) [IsFiniteMeasure η]
    [IsProbabilityMeasure (markedFirstArrivalStateMeasure ν η)] :
    (markedFirstArrivalStateMeasure ν η).map Prod.snd=(η univ)⁻¹ • η := by
  rw [markedFirstArrivalStateMeasure,Measure.map_map measurable_snd markedFirstEmbed_measurable]
  change ((markedFirstTimeMeasure ν η).prod η).map Prod.snd = _
  rw [Measure.map_snd_prod,markedFirstTimeMeasure_mass]

lemma markedFirstArrivalStateMeasure_mark (ν:Measure ℝ≥0) (η:Measure ℕ) [IsFiniteMeasure η]
    [IsProbabilityMeasure (markedFirstArrivalStateMeasure ν η)] (k:ℕ) :
    markedFirstArrivalStateMeasure ν η {p|p.2=k}=η {k}/η univ := by
  have he:=congrArg (fun μ:Measure ℕ=>μ {k}) (markedFirstArrivalStateMeasure_mark_marginal ν η)
  rw [Measure.map_apply measurable_snd (measurableSet_singleton k),Measure.smul_apply,smul_eq_mul] at he
  simpa only [Set.preimage,Set.mem_singleton_iff,ENNReal.div_eq_inv_mul] using he

lemma markedFirstArrivalStateMeasure_mark_real (ν:Measure ℝ≥0) (η:Measure ℕ) [IsFiniteMeasure η]
    [IsProbabilityMeasure (markedFirstArrivalStateMeasure ν η)] (k:ℕ) :
    (markedFirstArrivalStateMeasure ν η).real {p|p.2=k}=η.real {k}/η.real univ := by
  simp only [measureReal_def,markedFirstArrivalStateMeasure_mark,ENNReal.toReal_div]

lemma markedFirstArrivalMeasure_rectangle (ν:Measure ℝ≥0) (η:Measure ℕ) [IsFiniteMeasure η]
    (B:Set ℝ≥0) (k:ℕ) :
    markedFirstArrivalMeasure ν η (B×ˢ{k})=markedFirstTimeMeasure ν η B*η {k} := by
  exact Measure.prod_prod _ _
end WP.Probability
