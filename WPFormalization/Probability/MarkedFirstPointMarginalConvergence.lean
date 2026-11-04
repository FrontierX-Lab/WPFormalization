import WPFormalization.Probability.MarkedFirstPointMarginals
import Mathlib.MeasureTheory.Integral.Bochner.Set
/-! First-mark probabilities follow from genuine joint weak convergence by a
bounded continuous discrete-mark test. Only a.e. measurability of the actual
selector is used; no globally measurable representative is assumed. -/
noncomputable section
namespace WP.Probability
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

def markedFirstMarkTest (k : ℕ) : BoundedContinuousFunction MarkedFirstState ℝ :=
  (BoundedContinuousFunction.mkOfDiscrete (fun m : ℕ => if m = k then (1 : ℝ) else 0) 1
    (by intro m n;split_ifs <;> norm_num)).compContinuous ⟨Prod.snd, continuous_snd⟩

lemma integral_markedFirstMarkTest {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → MarkedFirstState) (hS : AEMeasurable S μ) (k : ℕ) :
    (∫ ω, markedFirstMarkTest k (S ω) ∂μ) = μ.real {ω | (S ω).2 = k} := by
  have hn : NullMeasurableSet {ω | (S ω).2 = k} μ := by
    simpa only [Set.preimage, Set.mem_singleton_iff, Function.comp_def] using
      ((measurable_snd.comp_aemeasurable hS).nullMeasurable (measurableSet_singleton k))
  have he : (fun ω => markedFirstMarkTest k (S ω)) =
      ({ω | (S ω).2 = k} : Set Ω).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp [markedFirstMarkTest, Set.indicator]
  rw [he, integral_indicator₀ hn, setIntegral_const, smul_eq_mul, mul_one]

lemma marked_first_point_mark_probability_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) (S : (n : ℕ) → Ω n → MarkedFirstState)
    (ν : Measure ℝ≥0) (η : Measure ℕ) [IsFiniteMeasure η]
    [IsProbabilityMeasure (markedFirstArrivalStateMeasure ν η)]
    (hS : ∀ᶠ n in atTop, AEMeasurable (S n) (μ n))
    (hLaw : LawConverges μ S (markedFirstArrivalStateMeasure ν η) id) (k : ℕ) :
    Tendsto (fun n => (μ n).real {ω | (S n ω).2 = k}) atTop
      (𝓝 (η.real {k} / η.real univ)) := by
  have ht := hLaw (markedFirstMarkTest k)
  have he : (∫ p, markedFirstMarkTest k (id p) ∂markedFirstArrivalStateMeasure ν η) =
      η.real {k} / η.real univ := by
    rw [integral_markedFirstMarkTest _ id aemeasurable_id]
    simpa only [id_eq] using markedFirstArrivalStateMeasure_mark_real ν η k
  rw [he] at ht
  apply ht.congr'
  filter_upwards [hS] with n hn
  exact integral_markedFirstMarkTest (μ n) (S n) hn k
end WP.Probability
