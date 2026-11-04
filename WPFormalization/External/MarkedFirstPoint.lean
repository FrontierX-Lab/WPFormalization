import WPFormalization.Probability.MarkedFirstPointDefinitions

/-! Explicit stage-one interfaces for two source-reviewed classical marked
first-point results. These structures add no axiom or deferred proof root:
consumers must pass their complete universally quantified fields explicitly.

The first interface is Last--Penrose, *Lectures on the Poisson Process*,
author manuscript 21 August 2017, Section 7.2, Theorem 7.4(i) with n = 1,
Corollary 7.5, and the measurable enumeration (7.7)/Exercise 7.4, pp.61--63.
Diffuse time intensity and finite positive mark measure give an ordinary
locally finite time projection and a unique finite first atom almost surely.

The second interface is a derived finite-window classical corollary of
Kallenberg, *Foundations of Modern Probability*, second edition (2002),
Theorems 4.27/4.28, pp.76--78, and Appendix A2.3. It is not a literal source
theorem. Finite-window atom matching at a unique first point, high-mark
no-escape, and the negligible invalid-selection event give approximation.
Neither interface contains a geometric object or a paper-specific estimate.
-/
noncomputable section
universe u
namespace WP.External
open WP.Probability Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- EXPLICIT_INTERFACE: the generic separable-intensity first-arrival law.
The infinite-state convention is irrelevant almost surely, since the time
intensity has infinite total mass and the mark measure has positive mass.
Its probability normalization is part of the same classical complete law. -/
structure MarkedPoissonFirstPointData : Prop where
  first_point_data : ∀ (ν : Measure ℝ≥0) [IsLocallyFiniteMeasure ν]
    [Measure.Regular ν] [NullSingletonClass ν] (η : Measure ℕ) [IsFiniteMeasure η],
    ν univ = ∞ → η univ ≠ 0 →
    ∀ (QL : ProbabilityMeasure (PointMeasure MarkedLengthSpace)),
    IsPoissonPointProcessLaw MarkedLengthSpace (ν.prod η) QL →
    IsProbabilityMeasure (markedFirstArrivalStateMeasure ν η) ∧
    ∃ F : PointMeasure MarkedLengthSpace → MarkedFirstState,
      AEMeasurable F QL ∧
      (∀ᵐ ξ ∂(QL : Measure _),
        MarkedTimePrefixFinite ξ ∧ IsUniqueFirstMarkedPoint ξ (F ξ)) ∧
      HasLaw F (markedFirstArrivalStateMeasure ν η) QL

/-- EXPLICIT_INTERFACE: generic first-point approximation, derived from
finite-window vague convergence and classical mapping/approximation. The
selector may depend on its entire probability space and use arbitrary ties.
All-mark prefix finiteness and high-mark no-escape are separate hypotheses;
they are not inferred from local finiteness of the marked point measure. -/
structure MarkedFirstPointConvergence : Prop where
  convergence : ∀ {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n))
    (Ξ : (n : ℕ) → Ω n → PointMeasure MarkedLengthSpace)
    (S : (n : ℕ) → Ω n → MarkedFirstState)
    (QL : ProbabilityMeasure (PointMeasure MarkedLengthSpace))
    (F : PointMeasure MarkedLengthSpace → MarkedFirstState),
    (∀ᶠ n in atTop, IsProbabilityMeasure (μ n)) →
    (∀ᶠ n in atTop, AEMeasurable (Ξ n) (μ n)) →
    (∀ᶠ n in atTop, AEMeasurable (S n) (μ n)) →
    AEMeasurable F QL →
    (∀ᵐ ξ ∂(QL : Measure _),
      MarkedTimePrefixFinite ξ ∧ IsUniqueFirstMarkedPoint ξ (F ξ)) →
    (∀ᶠ n in atTop, ∀ᵐ ω ∂μ n, MarkedTimePrefixFinite (Ξ n ω)) →
    Tendsto (fun n => (μ n) {ω | ¬IsFirstMarkedPoint (Ξ n ω) (S n ω)})
      atTop (𝓝 0) →
    MarkedNoEscape μ Ξ → LawConverges μ Ξ QL id →
    LawConverges μ S QL F

end WP.External
