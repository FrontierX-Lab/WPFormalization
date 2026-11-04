import WPFormalization.Probability.TwoColorPointMeasuresLaws
import Mathlib.Probability.Independence.Basic
noncomputable section
namespace WP.External
open WP.Probability MeasureTheory ProbabilityTheory
open scoped NNReal
/- Approved stage-one classical Prop scope; this definition asserts no instance.
Last--Penrose author manuscript 21 August 2017, Theorem 5.2 (printed p.39),
followed by Theorem 5.1 mapping the two disjoint clopen copies back to NNReal.
No WP object, kernel, moment estimate or convergence occurs.
The explicit premise remains a phase-two obligation; no instance or sorry is introduced. -/
def TwoColorPoissonRestrictionIndependence : Prop :=
  ∀ (ν μ : Measure ℝ≥0),
  ∀ [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ],
  ∀ (Q : ProbabilityMeasure (PointMeasure TwoColorSpace)),
    IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure ν μ) Q →
    IndepFun twoColorLeftProjection twoColorRightProjection
      (Q : Measure (PointMeasure TwoColorSpace))
end WP.External
