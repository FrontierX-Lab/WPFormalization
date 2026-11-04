import WPFormalization.Probability.PointMeasureDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Generic zero-count probability from discrete finite-dimensional Poisson law
convergence. All measure and convergence arguments below are proved in Lean;
this module adds no deferred classical input. -/

noncomputable section
namespace WP.Probability
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
universe u

def poissonZeroTest {d : ℕ} (i : Fin d) : BoundedContinuousFunction (Fin d → ℕ) ℝ :=
  BoundedContinuousFunction.mkOfDiscrete (fun z => if z i=0 then 1 else 0) 1 (by
    intro z w
    split_ifs <;> norm_num)

lemma integral_poissonZeroTest_comp {d : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin d → ℕ) (hX : Measurable X) (i : Fin d) :
    (∫ ω, poissonZeroTest i (X ω) ∂μ) = μ.real {ω | X ω i=0} := by
  have he : (fun ω => poissonZeroTest i (X ω)) =
      ({ω | X ω i=0} : Set Ω).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp [poissonZeroTest,Set.indicator]
  rw [he]
  exact integral_indicator_one ((measurableSet_singleton 0).preimage
    ((measurable_pi_apply i).comp hX))

lemma productPoissonMeasure_zero_coordinate {d : ℕ} (rates : Fin d → ℝ≥0)
    (i : Fin d) :
    (productPoissonMeasure rates).real {z | z i=0} = Real.exp (-(rates i : ℝ)) := by
  have hp := MeasureTheory.measurePreserving_eval (fun j : Fin d => poissonMeasure (rates j)) i
  have hm := hp.measure_preimage (measurableSet_singleton 0).nullMeasurableSet
  change (productPoissonMeasure rates {z | z i=0}).toReal = _
  have he : productPoissonMeasure rates {z | z i=0} = poissonMeasure (rates i) {0} := by
    simpa only [productPoissonMeasure,Set.preimage,Set.mem_singleton_iff] using hm
  rw [he]
  simpa [measureReal_def,poissonMeasure_real_singleton] using poissonMeasure_real_singleton (rates i) 0

lemma poisson_void_probability_tendsto {d : ℕ} {Ω : ℕ → Type u}
    [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → Measure (Ω n))
    (X : (n : ℕ) → Ω n → Fin d → ℕ) (rates : Fin d → ℝ≥0)
    (hX : ∀ᶠ n in atTop, Measurable (X n))
    (hlaw : LawConverges μ X (productPoissonMeasure rates) (fun z => z))
    (i : Fin d) :
    Tendsto (fun n => (μ n).real {ω | X n ω i=0}) atTop
      (𝓝 (Real.exp (-(rates i : ℝ)))) := by
  have ht := hlaw (poissonZeroTest i)
  have he : ∀ᶠ n in atTop,
      (∫ ω, poissonZeroTest i (X n ω) ∂μ n) = (μ n).real {ω | X n ω i=0} := by
    filter_upwards [hX] with n hn
    exact integral_poissonZeroTest_comp (μ n) (X n) hn i
  have hlim : (∫ z, poissonZeroTest i z ∂productPoissonMeasure rates) =
      Real.exp (-(rates i : ℝ)) := by
    calc
      _ = (productPoissonMeasure rates).real {z | z i=0} := by
        simpa only [id_eq] using integral_poissonZeroTest_comp
          (productPoissonMeasure rates) (fun z => z) measurable_id i
      _ = _ := productPoissonMeasure_zero_coordinate rates i
  rw [hlim] at ht
  exact ht.congr' he
end WP.Probability
