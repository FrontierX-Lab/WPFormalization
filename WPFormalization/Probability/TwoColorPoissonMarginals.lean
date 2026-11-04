import WPFormalization.Probability.TwoColorPointMeasuresLaws
import WPFormalization.External.PointProcessProbability
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace WP.Probability
open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

def twoColorLeftLaw (Q : ProbabilityMeasure (PointMeasure TwoColorSpace)) :
    ProbabilityMeasure (PointMeasure ℝ≥0) :=
  ⟨(Q : Measure (PointMeasure TwoColorSpace)).map twoColorLeftProjection,inferInstance⟩
def twoColorRightLaw (Q : ProbabilityMeasure (PointMeasure TwoColorSpace)) :
    ProbabilityMeasure (PointMeasure ℝ≥0) :=
  ⟨(Q : Measure (PointMeasure TwoColorSpace)).map twoColorRightProjection,inferInstance⟩

lemma twoColorLeftLaw_poisson
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure ν μ) Q) :
    IsPoissonPointProcessLaw ℝ≥0 ν (twoColorLeftLaw Q) := by
  intro d B hB
  have hBl : DisjointWindows TwoColorSpace (fun i => twoColorLeftWindow (B i)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have hxy := Sum.inl_injective he
    subst y
    exact Set.disjoint_left.mp (hB hij) hx hy
  have hh := hQ d (fun i => twoColorLeftWindow (B i)) hBl
  have he : windowRates TwoColorSpace (twoColorMeasure ν μ) (fun i => twoColorLeftWindow (B i))=
      windowRates ℝ≥0 ν B := by
    funext i
    exact congrArg ENNReal.toNNReal (twoColorMeasure_inl ν μ (B i).carrier (B i).measurableSet)
  rw [he] at hh
  have hm : Measurable (windowCountVector ℝ≥0 B) := by
    apply Measurable.of_eval
    intro i
    exact WP.External.pointMeasure_count_measurable ℝ≥0 (B i)
  refine ⟨hm.aemeasurable,?_⟩
  change Measure.map (windowCountVector ℝ≥0 B)
    (Measure.map twoColorLeftProjection (Q : Measure (PointMeasure TwoColorSpace)))=_
  rw [Measure.map_map hm twoColorLeftProjection_continuous.measurable]
  have hecomp : (windowCountVector ℝ≥0 B ∘ twoColorLeftProjection)=
      windowCountVector TwoColorSpace (fun i => twoColorLeftWindow (B i)) := by
    funext ξ i
    exact twoColorLeftProjection_count ξ (B i)
  rw [hecomp]
  exact hh.map_eq

lemma twoColorRightLaw_poisson
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure ν μ) Q) :
    IsPoissonPointProcessLaw ℝ≥0 μ (twoColorRightLaw Q) := by
  intro d B hB
  have hBl : DisjointWindows TwoColorSpace (fun i => twoColorRightWindow (B i)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have hxy := Sum.inr_injective he
    subst y
    exact Set.disjoint_left.mp (hB hij) hx hy
  have hh := hQ d (fun i => twoColorRightWindow (B i)) hBl
  have he : windowRates TwoColorSpace (twoColorMeasure ν μ) (fun i => twoColorRightWindow (B i))=
      windowRates ℝ≥0 μ B := by
    funext i
    exact congrArg ENNReal.toNNReal (twoColorMeasure_inr ν μ (B i).carrier (B i).measurableSet)
  rw [he] at hh
  have hm : Measurable (windowCountVector ℝ≥0 B) := by
    apply Measurable.of_eval
    intro i
    exact WP.External.pointMeasure_count_measurable ℝ≥0 (B i)
  refine ⟨hm.aemeasurable,?_⟩
  change Measure.map (windowCountVector ℝ≥0 B)
    (Measure.map twoColorRightProjection (Q : Measure (PointMeasure TwoColorSpace)))=_
  rw [Measure.map_map hm twoColorRightProjection_continuous.measurable]
  have hecomp : (windowCountVector ℝ≥0 B ∘ twoColorRightProjection)=
      windowCountVector TwoColorSpace (fun i => twoColorRightWindow (B i)) := by
    funext ξ i
    exact twoColorRightProjection_count ξ (B i)
  rw [hecomp]
  exact hh.map_eq

end WP.Probability
