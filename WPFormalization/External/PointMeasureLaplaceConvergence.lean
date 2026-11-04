import WPFormalization.Probability.PointMeasureLaplaceTests
noncomputable section
universe u v
namespace WP.External
open WP.Probability MeasureTheory Filter
open scoped NNReal Topology CompactlySupported
/- Approved stage-one classical Prop scope, no instance or theorem assertion.
Kallenberg (2002), Theorem 16.16(i)<->(ii), pp.316--317,
and Theorem 5.3 Laplace continuity on nonnegative random variables, pp.86--87.
For each nonnegative compact continuous f, apply transform continuity to
its nonnegative integral, using every nonnegative scalar multiple t*f.
This applies to all genuine locally finite counting measures with multiplicity;
no simplicity or PPP assumption is made. Phase two must prove this Prop. -/
def PointMeasureLaplaceConvergence : Prop :=
  ∀ (Ω : ℕ → Type u) [∀ j, MeasurableSpace (Ω j)]
    (Ωlimit : Type v) [MeasurableSpace Ωlimit]
    (μ : (j : ℕ) → Measure (Ω j))
    (X : (j : ℕ) → Ω j → PointMeasure ℝ≥0)
    (Q : Measure Ωlimit) [IsProbabilityMeasure Q]
    (Z : Ωlimit → PointMeasure ℝ≥0),
    (∀ᶠ j in atTop, IsProbabilityMeasure (μ j)) →
    (∀ᶠ j in atTop, AEMeasurable (X j) (μ j)) →
    AEMeasurable Z Q →
    (∀ f : C_c(ℝ≥0, ℝ), (∀ x, 0 ≤ f x) →
      Tendsto (fun j => ∫ ω, PoissonCluster.laplaceObservable (fun x => f x) (X j ω) ∂μ j)
        atTop (𝓝 (∫ ω, PoissonCluster.laplaceObservable (fun x => f x) (Z ω) ∂Q))) →
    LawConverges μ X Q Z
end WP.External
