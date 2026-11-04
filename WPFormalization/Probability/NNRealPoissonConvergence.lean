import WPFormalization.Probability.NNRealWindowBasis
import WPFormalization.External.PointProcessProbability

/-! A proved half-line specialization of the registered classical criteria.
Actual prefix counts and all disjoint rational-window factorial moments imply
weak convergence in the genuine compact-support-integral vague topology. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

/-- No geometry or moment estimate is assumed by a new external field here:
this is the direct local composition of the generic classical results. -/
theorem nnreal_poisson_limit_of_rational_mixed_factorials
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n))
    (Ξ : (n : ℕ) → Ω n → PointMeasure ℝ≥0)
    (hprob : ∀ᶠ n in atTop, IsProbabilityMeasure (μ n))
    (hprefix : ∀ᶠ n in atTop, ∀ b : ℝ≥0,
      AEMeasurable (fun ω => (Ξ n ω).count ℝ≥0 (nnrealPrefixWindow b)) (μ n))
    (ν : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    [NullSingletonClass ν]
    (hmom : ∀ d : ℕ, ∀ B : Fin d → RelCompactBorelWindow ℝ≥0,
      (∀ i, B i ∈ nnrealRationalWindows) → DisjointWindows ℝ≥0 B →
      MixedFactorialMomentLimit μ
        (fun n ω => windowCountVector ℝ≥0 B (Ξ n ω)) (windowRates ℝ≥0 ν B)) :
    ∃ Q : ProbabilityMeasure (PointMeasure ℝ≥0),
      IsPoissonPointProcessLaw ℝ≥0 ν Q ∧ LawConverges μ Ξ Q (fun ξ => ξ) := by
  obtain ⟨Q, hQ⟩ := WP.External.poisson_point_process_exists ℝ≥0 ν
  refine ⟨Q, hQ, ?_⟩
  apply WP.External.pointMeasure_vague_of_semiring_mixed_factorials ℝ≥0
    μ Ξ hprob ?_ ν nnrealRationalWindows (nnrealRationalWindows_basis ν) Q hQ hmom
  filter_upwards [hprefix] with n hn
  exact WP.External.pointMeasure_nnreal_aemeasurable_of_prefix_counts (μ n) (Ξ n) hn

end WP.Probability
