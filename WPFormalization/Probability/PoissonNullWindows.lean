import WPFormalization.Probability.FinitePoissonSums
noncomputable section
set_option maxHeartbeats 0
universe u
namespace WP.Probability
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

lemma poisson_pointMeasure_null_window
    (E : Type u) [TopologicalSpace E] [MeasurableSpace E]
    (ν : Measure E) [IsFiniteMeasureOnCompacts ν]
    (Q : ProbabilityMeasure (PointMeasure E)) (hQ : IsPoissonPointProcessLaw E ν Q)
    (W : RelCompactBorelWindow E) (hν : ν W.carrier=0) :
    ∀ᵐξ ∂(Q : Measure (PointMeasure E)),ξ.toMeasure W.carrier=0 := by
  let B : Fin 1 → RelCompactBorelWindow E := fun _ => W
  have hd : DisjointWindows E B := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hv := hQ 1 B hd
  let r : Fin 1 → ℝ≥0 := windowRates E ν B
  have he : HasLaw (fun z : Fin 1 → ℕ => z 0) (poissonMeasure (r 0)) (productPoissonMeasure r) :=
    (measurePreserving_eval (fun i => poissonMeasure (r i)) (0:Fin 1)).hasLaw
  have hc := he.fun_comp hv
  have hr : r 0=0 := by simp [r,windowRates,B,hν]
  rw [hr,poissonMeasure_zero_eq_dirac] at hc
  have ha := hc.ae_eq_of_dirac
  filter_upwards [ha] with ξ hξ
  rw [PointMeasure.count_spec E ξ W]
  have hcount : ξ.count E W=0 := hξ
  simp only [hcount,Nat.cast_zero]

lemma poisson_pointMeasure_no_atom_at
    (ν : Measure ℝ≥0) [IsLocallyFiniteMeasure ν]
    (Q : ProbabilityMeasure (PointMeasure ℝ≥0)) (hQ : IsPoissonPointProcessLaw ℝ≥0 ν Q)
    (s : ℝ≥0) (hν : ν {s}=0) :
    ∀ᵐξ ∂(Q : Measure (PointMeasure ℝ≥0)),ξ.toMeasure {s}=0 := by
  let W : RelCompactBorelWindow ℝ≥0 :=
    ⟨{s},measurableSet_singleton s,by rw [isClosed_singleton.closure_eq];exact isCompact_singleton⟩
  exact poisson_pointMeasure_null_window ℝ≥0 ν Q hQ W hν

end WP.Probability
