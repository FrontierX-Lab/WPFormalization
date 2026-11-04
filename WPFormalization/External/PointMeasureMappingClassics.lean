import WPFormalization.Probability.PointMeasureDefinitions
import Mathlib.Topology.Metrizable.Basic
noncomputable section
universe u v w z
namespace WP.External
open WP.Probability MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology
/- Explicit classical interface, source/type approved by the root audit.
Kallenberg (2002), A2.3(iii),(iv), pp.564–565: bounded compact Borel
pairings are Borel and continuous at measures charging no discontinuities.
This is the generic compact-test corollary, not a literal theorem quotation.
It contains no pants geometry, proper-support premise, or WP convergence. -/
def CompactBorelVaguePairing : Prop :=
  ∀ (h : ℝ≥0 → ℝ), Measurable h →
    (∃ C : ℝ, ∀ x, ‖h x‖ ≤ C) →
    (∃ K : Set ℝ≥0, IsCompact K ∧ Function.support h ⊆ K) →
    Measurable (fun ξ : PointMeasure ℝ≥0 => ∫ x, h x ∂ξ.toMeasure) ∧
      ∀ ξ : PointMeasure ℝ≥0,
        (∀ᵐ x ∂ξ.toMeasure, ContinuousAt h x) →
        ContinuousAt (fun η : PointMeasure ℝ≥0 => ∫ x, h x ∂η.toMeasure) ξ

/- The fixed-map special case of Kallenberg Theorem 4.27, pp.76-77,
with changing source probability spaces. No point-process or geometry data. -/
def AlmostSureContinuousMapping : Prop :=
  ∀ (E : Type u) [TopologicalSpace E] [MetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (F : Type v) [TopologicalSpace F] [MetrizableSpace F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
    (Ω : ℕ → Type w) [∀ j, MeasurableSpace (Ω j)]
    (Ωlimit : Type z) [MeasurableSpace Ωlimit]
    (μ : (j : ℕ) → Measure (Ω j)) (X : (j : ℕ) → Ω j → E)
    (Q : Measure Ωlimit) [IsProbabilityMeasure Q] (Z : Ωlimit → E)
    (f : E → F),
    (∀ᶠ j in atTop, IsProbabilityMeasure (μ j)) →
    (∀ᶠ j in atTop, AEMeasurable (X j) (μ j)) →
    AEMeasurable Z Q → Measurable f →
    (∀ᵐ ω ∂Q, ContinuousAt f (Z ω)) →
    LawConverges μ X Q Z →
    LawConverges μ (fun j ω => f (X j ω)) Q (fun ω => f (Z ω))
end WP.External
