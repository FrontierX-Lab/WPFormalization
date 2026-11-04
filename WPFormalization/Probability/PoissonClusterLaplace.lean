import WPFormalization.Probability.PoissonClusterDefinitions
import WPFormalization.External.PoissonLaplaceFunctional

/- Local consequences of the registered generic PPP Laplace formula.
In particular, the independent two-PPP calculation is an ordinary product
measure integral identity; independence or geometry is not an extra field. -/
noncomputable section
universe u
namespace WP.Probability.PoissonCluster
open MeasureTheory Set
open scoped ENNReal NNReal Topology
variable (E : Type u) [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [T2Space E] [LocallyCompactSpace E] [SecondCountableTopology E]

lemma poisson_laplace_observable_integrable
    (ν : Measure E) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    (QL : ProbabilityMeasure (PointMeasure E)) (hPPP : IsPoissonPointProcessLaw E ν QL)
    (h : E→ℝ) (hh : Measurable h) (hn : ∀x,0≤h x)
    (hb : ∃C : ℝ,∀x,h x≤C) (hs : ∃K : Set E,IsCompact K ∧ Function.support h⊆K) :
    Integrable h ν ∧ (∀ξ : PointMeasure E,Integrable h ξ.toMeasure) ∧
      Integrable (laplaceObservable h) (QL : Measure (PointMeasure E)) := by
  refine ⟨integrable_of_bounded_nonneg_compact_support ν h hh hn hb hs,
    fun ξ=>integrable_of_bounded_nonneg_compact_support ξ.toMeasure h hh hn hb hs,?_⟩
  exact laplaceObservable_integrable h hn QL
    (WP.External.poisson_laplace_functional E ν QL hPPP h hh hn hb hs).1

theorem independent_poisson_laplace_formula
    (ν μ : Measure E) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    [IsLocallyFiniteMeasure μ] [Measure.Regular μ]
    (QN QP : ProbabilityMeasure (PointMeasure E))
    (hN : IsPoissonPointProcessLaw E ν QN) (hP : IsPoissonPointProcessLaw E μ QP)
    (h k : E→ℝ) (hh : Measurable h) (hk : Measurable k)
    (hn : ∀x,0≤h x) (kn : ∀x,0≤k x)
    (hb : ∃C : ℝ,∀x,h x≤C) (kb : ∃C : ℝ,∀x,k x≤C)
    (hs : ∃K : Set E,IsCompact K ∧ Function.support h⊆K)
    (ks : ∃K : Set E,IsCompact K ∧ Function.support k⊆K) :
    (∫ξ,jointLaplaceObservable h k ξ ∂(QN : Measure (PointMeasure E)).prod QP)=
      Real.exp (-(∫x,1-Real.exp (-h x) ∂ν)-(∫x,1-Real.exp (-k x) ∂μ)) := by
  rw [independent_laplace_integral_eq_mul]
  simp only [laplaceObservable]
  rw [(WP.External.poisson_laplace_functional E ν QN hN h hh hn hb hs).2,
    (WP.External.poisson_laplace_functional E μ QP hP k hk kn kb ks).2]
  rw [←Real.exp_add]
  congr 1

end WP.Probability.PoissonCluster
