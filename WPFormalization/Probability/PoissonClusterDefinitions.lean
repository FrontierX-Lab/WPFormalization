import WPFormalization.Probability.PointMeasureDefinitions
import Mathlib.MeasureTheory.Integral.Prod

/- Generic Poisson cluster objects and elementary real Laplace identities.
The indexed cluster measure is the actual sum of pushforwards of the input
point measure restricted to positive parent locations. No stochastic law,
local finiteness or proper-support conclusion is a definition field. -/
noncomputable section
universe u v
namespace WP.Probability.PoissonCluster
open MeasureTheory Set
open scoped ENNReal NNReal Topology

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E]

def laplaceObservable (h : E→ℝ) (ξ : PointMeasure E) : ℝ :=
  Real.exp (-(∫x,h x ∂ξ.toMeasure))

def jointLaplaceObservable (h k : E→ℝ) (ξ : PointMeasure E × PointMeasure E) : ℝ :=
  Real.exp (-(∫x,h x ∂ξ.1.toMeasure)-(∫x,k x ∂ξ.2.toMeasure))

lemma jointLaplaceObservable_eq_mul (h k : E→ℝ) (ξ : PointMeasure E × PointMeasure E) :
    jointLaplaceObservable h k ξ=laplaceObservable h ξ.1*laplaceObservable k ξ.2 := by
  simp only [jointLaplaceObservable,laplaceObservable,sub_eq_add_neg,Real.exp_add]

lemma laplaceObservable_nonneg (h : E→ℝ) (ξ : PointMeasure E) :
    0≤laplaceObservable h ξ := (Real.exp_pos _).le

lemma laplaceObservable_le_one (h : E→ℝ) (hh : ∀x,0≤h x) (ξ : PointMeasure E) :
    laplaceObservable h ξ≤1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (integral_nonneg hh)

lemma laplaceObservable_integrable (h : E→ℝ) (hh : ∀x,0≤h x)
    (μ : Measure (PointMeasure E)) [IsFiniteMeasure μ]
    (hm : Measurable (laplaceObservable h)) : Integrable (laplaceObservable h) μ := by
  apply Integrable.mono' (integrable_const (1:ℝ)) hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ξ
  rw [Real.norm_eq_abs,abs_of_nonneg (laplaceObservable_nonneg h ξ)]
  exact laplaceObservable_le_one h hh ξ

lemma independent_laplace_integral_eq_mul (h k : E→ℝ)
    (μ ν : Measure (PointMeasure E)) [SFinite μ] [SFinite ν] :
    (∫ξ,jointLaplaceObservable h k ξ ∂μ.prod ν)=
      (∫ξ,laplaceObservable h ξ ∂μ)*(∫ξ,laplaceObservable k ξ ∂ν) := by
  simp only [jointLaplaceObservable_eq_mul]
  exact integral_prod_mul _ _

/- Actual indexed clusters, retaining all multiplicities. In applications
J is the marked primitive unoriented catalog of the reference pants. -/
def indexedClusterMeasure {J : Type v} (length : J→ℝ≥0→ℝ≥0)
    (ξ : Measure ℝ≥0) : Measure ℝ≥0 :=
  Measure.sum (fun γ : J=>(ξ.restrict (Ioi (0:ℝ≥0))).map (length γ))

variable [BorelSpace E] [T2Space E] [LocallyCompactSpace E]

lemma integrable_of_bounded_nonneg_compact_support (μ : Measure E)
    [IsLocallyFiniteMeasure μ] (h : E→ℝ) (hm : Measurable h) (hn : ∀x,0≤h x)
    (hb : ∃C : ℝ,∀x,h x≤C) (hs : ∃K : Set E,IsCompact K ∧ Function.support h⊆K) :
    Integrable h μ := by
  obtain ⟨C,hC⟩:=hb
  obtain ⟨K,hK,hsK⟩:=hs
  apply (integrableOn_iff_integrable_of_support_subset hsK).mp
  apply Measure.integrableOn_of_bounded hK.measure_lt_top.ne hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hn x)] using hC x

end WP.Probability.PoissonCluster
