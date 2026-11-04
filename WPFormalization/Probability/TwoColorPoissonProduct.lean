import WPFormalization.External.PoissonRestrictionIndependence
import WPFormalization.Probability.TwoColorPoissonMarginals
noncomputable section
namespace WP.Probability
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

lemma twoColorDecode_map_eq_product
    (C : WP.External.TwoColorPoissonRestrictionIndependence)
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure ν μ) Q) :
    (Q : Measure (PointMeasure TwoColorSpace)).map twoColorDecode =
      (twoColorLeftLaw Q : Measure (PointMeasure ℝ≥0)).prod (twoColorRightLaw Q) := by
  exact (C ν μ Q hQ).map_prod_eq_prod_map_map
    twoColorLeftProjection_continuous.measurable.aemeasurable
    twoColorRightProjection_continuous.measurable.aemeasurable

lemma twoColor_poisson_independent_marginals
    (C : WP.External.TwoColorPoissonRestrictionIndependence)
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure ν μ) Q) :
    IndepFun twoColorLeftProjection twoColorRightProjection (Q : Measure (PointMeasure TwoColorSpace)) ∧
      IsPoissonPointProcessLaw ℝ≥0 ν (twoColorLeftLaw Q) ∧
      IsPoissonPointProcessLaw ℝ≥0 μ (twoColorRightLaw Q) :=
  ⟨C ν μ Q hQ,twoColorLeftLaw_poisson ν μ Q hQ,twoColorRightLaw_poisson ν μ Q hQ⟩

end WP.Probability
