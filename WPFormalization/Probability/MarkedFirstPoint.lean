import WPFormalization.External.MarkedFirstPoint
import WPFormalization.Probability.MarkedFirstPointMarginals

/-! Local consumers of the two explicit classical first-point interfaces.
The genuine first-state target and all geometric-free normalization are
retained; no paper-specific limit law is supplied as an interface field. -/
noncomputable section
universe u
namespace WP.Probability
open WP.External Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

lemma markedFirstArrivalStateMeasure_isProbabilityMeasure
    (D : MarkedPoissonFirstPointData)
    (ν : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    [NullSingletonClass ν] (η : Measure ℕ) [IsFiniteMeasure η]
    (hν : ν univ = ∞) (hη : η univ ≠ 0)
    (QL : ProbabilityMeasure (PointMeasure MarkedLengthSpace))
    (hPPP : IsPoissonPointProcessLaw MarkedLengthSpace (ν.prod η) QL) :
    IsProbabilityMeasure (markedFirstArrivalStateMeasure ν η) :=
  (D.first_point_data ν η hν hη QL hPPP).1

lemma lawConverges_marked_first_point
    (D : MarkedPoissonFirstPointData) (FC : MarkedFirstPointConvergence.{u})
    (ν : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    [NullSingletonClass ν] (η : Measure ℕ) [IsFiniteMeasure η]
    (hν : ν univ = ∞) (hη : η univ ≠ 0)
    (QL : ProbabilityMeasure (PointMeasure MarkedLengthSpace))
    (hPPP : IsPoissonPointProcessLaw MarkedLengthSpace (ν.prod η) QL)
    {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n))
    (Ξ : (n : ℕ) → Ω n → PointMeasure MarkedLengthSpace)
    (S : (n : ℕ) → Ω n → MarkedFirstState)
    (hprob : ∀ᶠ n in atTop, IsProbabilityMeasure (μ n))
    (hΞ : ∀ᶠ n in atTop, AEMeasurable (Ξ n) (μ n))
    (hS : ∀ᶠ n in atTop, AEMeasurable (S n) (μ n))
    (hprefix : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ n, MarkedTimePrefixFinite (Ξ n ω))
    (hvalid : Tendsto (fun n => (μ n) {ω | ¬IsFirstMarkedPoint (Ξ n ω) (S n ω)})
      atTop (𝓝 0))
    (hescape : MarkedNoEscape μ Ξ) (hLaw : LawConverges μ Ξ QL id) :
    IsProbabilityMeasure (markedFirstArrivalStateMeasure ν η) ∧
    LawConverges μ S (markedFirstArrivalStateMeasure ν η) id := by
  obtain ⟨hp, F, hF, hQ, hFLaw⟩ := D.first_point_data ν η hν hη QL hPPP
  refine ⟨hp, ?_⟩
  have ht := FC.convergence μ Ξ S QL F hprob hΞ hS hF hQ hprefix hvalid hescape hLaw
  intro f
  have he := hFLaw.integral_comp f.continuous.measurable.aestronglyMeasurable
  simpa only [Function.comp_def, id_eq] using (he ▸ ht f)

end WP.Probability
