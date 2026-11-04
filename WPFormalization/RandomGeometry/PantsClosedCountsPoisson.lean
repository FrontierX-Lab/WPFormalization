import WPFormalization.RandomGeometry.PantsClosedPointProcessMoments
import WPFormalization.External.PointProcessProbability

/-! The closed-interval count assertion in original Theorem 14.1(i), with
its actual geodesic counts and independent Poisson target. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

lemma pantsLengthPointProcess_aemeasurable {g n : ℕ}
    (μ : Measure (G.Moduli g n (fun _ => 0))) :
    AEMeasurable (fun X => pantsLengthPointProcess H X) μ := by
  apply WP.External.pointMeasure_nnreal_aemeasurable_of_prefix_counts μ
  intro b
  simp_rw [pantsLengthPointProcess,planarLengthPointMeasure_prefix_count]
  exact (H.measurable_planarCount g n 2 _).aemeasurable

include C MI in
 theorem pants_closed_interval_counts_poisson_measure_rates (d : ℕ) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d → ℝ≥0) (horder : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j k => Disjoint (Icc (lo j) (hi j)) (Icc (lo k) (hi k)))) :
    LawConverges (fun g => wpProbability G g (n g))
      (fun g X => windowCountVector ℝ≥0 (fun j => lengthIccWindow (lo j) (hi j))
        (pantsLengthPointProcess H X))
      (productPoissonMeasure (windowRates ℝ≥0 quadraticLengthIntensity
        (fun j => lengthIccWindow (lo j) (hi j)))) (fun z => z) := by
  apply WP.External.factorial_moments_poisson_nonneg
    (fun g => wpProbability G g (n g))
    (fun g X => windowCountVector ℝ≥0 (fun j => lengthIccWindow (lo j) (hi j))
      (pantsLengthPointProcess H X))
    (WP.Spectral.wpProbability_eventually_probability P G n
      ((pants_fast_cusps_tendsto_atTop n hnfast).eventually_ge_atTop 1)) ?_ _
    (pants_point_process_Icc_mixedFactorialMomentLimit G H T C MI d n hnfast lo hi horder hdis)
  filter_upwards [] with g
  apply aemeasurable_pi_lambda
  intro i
  exact (WP.External.pointMeasure_count_measurable ℝ≥0
    (lengthIccWindow (lo i) (hi i))).comp_aemeasurable
      (pantsLengthPointProcess_aemeasurable G H (wpProbability G g (n g)))

include C MI in
 theorem pants_closed_interval_counts_poisson (d : ℕ) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d → ℝ≥0) (horder : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j k => Disjoint (Icc (lo j) (hi j)) (Icc (lo k) (hi k)))) :
    LawConverges (fun g => wpProbability G g (n g))
      (fun g X => windowCountVector ℝ≥0 (fun j => lengthIccWindow (lo j) (hi j))
        (pantsLengthPointProcess H X))
      (productPoissonMeasure (fun j => Real.toNNReal ((hi j : ℝ)^2-(lo j : ℝ)^2)))
      (fun z => z) := by
  have hrates : windowRates ℝ≥0 quadraticLengthIntensity
      (fun j => lengthIccWindow (lo j) (hi j)) =
      fun j => Real.toNNReal ((hi j : ℝ)^2-(lo j : ℝ)^2) := by
    funext j
    change (quadraticLengthIntensity (Icc (lo j) (hi j))).toNNReal = _
    rw [quadraticLengthIntensity_Icc]
    rfl
  have hh := pants_closed_interval_counts_poisson_measure_rates G H T C MI d n hnfast
    lo hi horder hdis
  rw [hrates] at hh
  exact hh

end WP.RandomGeometry
