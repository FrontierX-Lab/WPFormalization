import WPFormalization.RandomGeometry.PantsRationalMoments
import WPFormalization.Probability.NNRealPoissonConvergence

/-! Actual two-cusp pants converge to the genuine vague PPP with intensity
2t dt on [0,∞). This is the process assertion of original Theorem 14.1(i),
not a declaration that all clauses of Theorem 14.1 have been completed. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

lemma pantsLengthPointProcess_prefix_count_measurable {g n : ℕ} (b : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      (pantsLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow b)) := by
  simp_rw [pantsLengthPointProcess,planarLengthPointMeasure_prefix_count]
  exact H.measurable_planarCount g n 2 _

include C MI in
/- Original (14.2) for the actual same-H geodesics. The transparent positive
scale extension is proved eventually exactly sqrt(q_g), and no density limit
or artificial all-g positivity/stability assumption is introduced. -/
theorem pants_poisson_process (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop) :
    ∃ Q : ProbabilityMeasure (PointMeasure ℝ≥0),
      IsPoissonPointProcessLaw ℝ≥0 quadraticLengthIntensity Q ∧
      LawConverges (fun g => wpProbability G g (n g))
        (fun g (X : G.Moduli g (n g) (fun _ => 0)) => pantsLengthPointProcess H X)
        Q (fun ξ => ξ) := by
  have hn := pants_fast_cusps_tendsto_atTop n hnfast
  apply nnreal_poisson_limit_of_rational_mixed_factorials
    (fun g => wpProbability G g (n g))
    (fun g (X : G.Moduli g (n g) (fun _ => 0)) => pantsLengthPointProcess H X)
    (WP.Spectral.wpProbability_eventually_probability P G n (hn.eventually_ge_atTop 1))
    ?_ quadraticLengthIntensity
    (pants_point_process_semiring_mixed_factorials G H T C MI n hnfast)
  filter_upwards [] with g
  intro b
  exact (pantsLengthPointProcess_prefix_count_measurable G H b).aemeasurable

end WP.RandomGeometry
