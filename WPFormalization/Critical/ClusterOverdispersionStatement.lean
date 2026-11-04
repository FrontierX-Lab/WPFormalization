import WPFormalization.Critical.ClusterWindowCounts
import Mathlib.Analysis.SpecialFunctions.Arcosh
import WPFormalization.Probability.TwoColorPointMeasuresIntensities

/-! Literal scope of (14.22) and the following non-Poisson deduction.
The declaration is kept separate from its proof. No finite-genus moment
convergence is included. -/
noncomputable section
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory ProbabilityTheory WP.Probability
open scoped NNReal ENNReal

structure ClusterOverdispersionConclusion (F : Family.{u, v}) (c : ℝ)
    (Q : ProbabilityMeasure (PointMeasure ℝ≥0)) : Prop where
  finite_moments : ∀ (L : ℝ≥0) (n : ℕ), MemLp (prefixCount L) n Q
  variance_excess : ∀ L : ℝ≥0,
    variance (prefixCount L) Q - (∫ ξ, prefixCount L ξ ∂Q) =
      ∫ s, windowMultiplicity F L s * (windowMultiplicity F L s - 1)
        ∂criticalPantsLengthIntensity c
  strict_excess : ∀ L : ℝ≥0, 2 * Real.arcosh 3 < L →
    (∫ ξ, prefixCount L ξ ∂Q) < variance (prefixCount L) Q
  not_poisson : ∀ (ρ : Measure ℝ≥0) [IsLocallyFiniteMeasure ρ],
    ¬ IsPoissonPointProcessLaw ℝ≥0 ρ Q
end WP.Critical.PantsCluster
