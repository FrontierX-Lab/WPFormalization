import WPFormalization.Probability.PointMeasureDefinitions

/- Approved stage-one classical probability dependency PROB-POISSON-LAPLACE.
Kallenberg, Foundations of Modern Probability, second edition (2002),
Chapter 12, Lemma 12.2(i), printed p.227; random-integral measurability is
recorded at the start of the chapter, printed p.225. Independently:
Last--Penrose, Lectures on the Poisson Process, author manuscript dated
21 August 2017, Theorem 3.9, printed pp.23--24.

This is the bounded nonnegative compactly supported Borel specialization
on an lcsc Hausdorff Borel space. The genuine PPP is the existing law
specified by actual disjoint-set Poisson counts. Multiplicities and zero
intensities are permitted. No geometric object or convergence is asserted.
The single sorry remains an explicit unproved classical dependency. -/
noncomputable section
universe u
namespace WP.External
open WP.Probability MeasureTheory Set
open scoped Topology

theorem poisson_laplace_functional
    (E : Type u) [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [T2Space E] [LocallyCompactSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    (QL : ProbabilityMeasure (PointMeasure E)) (hPPP : IsPoissonPointProcessLaw E ν QL)
    (h : E→ℝ) (hh : Measurable h) (hnonneg : ∀x,0≤h x)
    (hbound : ∃C : ℝ,∀x,h x≤C)
    (hsupport : ∃K : Set E,IsCompact K ∧ Function.support h⊆K) :
    Measurable (fun ξ : PointMeasure E=>Real.exp (-(∫x,h x ∂ξ.toMeasure))) ∧
    (∫ξ : PointMeasure E,Real.exp (-(∫x,h x ∂ξ.toMeasure)) ∂QL)=
      Real.exp (-(∫x,1-Real.exp (-h x) ∂ν)) := by
  sorry

end WP.External
