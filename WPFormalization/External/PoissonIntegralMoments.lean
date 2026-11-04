import WPFormalization.Probability.PointMeasureDefinitions
import Mathlib.Probability.Moments.Variance

/-! Classical moments of bounded, compactly supported Poisson integrals. -/

noncomputable section
namespace WP.External
open WP.Probability MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Classical Campbell and Poisson second-moment formulas, restricted to bounded
Borel functions supported in a compact interval. Last--Penrose (2017),
Proposition 2.7 and equation (4.26). All finite moments follow by domination
by the count of the support, a finite-rate Poisson variable (Chapter 1).
This is an explicit stage-one input, with no asserted instance. It contains
no pants geometry, cluster kernel, or paper-specific conclusion. -/
structure PoissonIntegralMoments : Prop where
  moments : ∀ (μ : Measure ℝ≥0) [IsLocallyFiniteMeasure μ]
    (Q : ProbabilityMeasure (PointMeasure ℝ≥0)),
    IsPoissonPointProcessLaw ℝ≥0 μ Q →
    ∀ (f : ℝ≥0 → ℝ), Measurable f →
    (∃ C : ℝ, ∀ s, ‖f s‖ ≤ C) →
    (∃ R : ℝ≥0, Function.support f ⊆ Iic R) →
    (∀ n : ℕ, MemLp (fun ξ : PointMeasure ℝ≥0 => ∫ s, f s ∂ξ.toMeasure) n Q) ∧
    (∫ ξ : PointMeasure ℝ≥0, (∫ s, f s ∂ξ.toMeasure) ∂Q) = ∫ s, f s ∂μ ∧
    variance (fun ξ : PointMeasure ℝ≥0 => ∫ s, f s ∂ξ.toMeasure) Q =
      ∫ s, (f s)^2 ∂μ
end WP.External
