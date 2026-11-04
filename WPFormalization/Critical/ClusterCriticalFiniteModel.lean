import WPFormalization.Critical.ClusterTwoColorMapping
import WPFormalization.Critical.MixedPoissonConsumer
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd u v
namespace WP.Critical.PantsCluster
open WP.External WP.External.PantsCluster WP.RandomGeometry WP.Probability MeasureTheory Filter Set
open scoped Classical ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)

include MI in
lemma critical_parent_pair_aemeasurable (g n : ℕ) :
    AEMeasurable (fun X : G.Moduli g n (fun _ => 0) =>
      (nonseparatingLengthPointMeasure T X,planarLengthPointMeasure H X 1 (by norm_num) 2))
      (wpProbability G g n) := by
  apply AEMeasurable.prodMk
  · apply WP.External.pointMeasure_nnreal_aemeasurable_of_prefix_counts
    intro b
    exact (nonseparatingLengthPointMeasure_measurable_count T MI (nnrealPrefixWindow b)).aemeasurable
  · apply WP.External.pointMeasure_nnreal_aemeasurable_of_prefix_counts
    intro b
    simp_rw [planarLengthPointMeasure_prefix_count]
    exact (H.measurable_planarCount g n 2 _).aemeasurable

/- Internal actual-parent consumer. The short-intersection hypothesis is
explicitly the unfinished G3 input, not a new classical probability field.
The observed process here is a canonical finite-cluster model built from
actual WP parent curves, not yet the ambient full primitive spectrum. -/
include MI RG in
lemma critical_compactClusterSuperposition_of_short_intersections
    (F : Family.{u,v}) (D : DeformationClassics F)
    (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,bb,0})
    (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (hshort : ∀t : ℕ,2≤t→∀L : ℝ,0≤L→Tendsto
      (fun g => ∫⁻ X,allShortIntersectingSimpleTupleCount T X t L
        ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    ∃Q : ProbabilityMeasure (PointMeasure TwoColorSpace),
      IsPoissonPointProcessLaw TwoColorSpace (criticalTwoColorIntensity c) Q ∧
      ∀(ε R : ℝ≥0),0<ε→LawConverges (fun g => wpProbability G g (n g))
        (fun g X => compactClusterSuperposition F D ε R
          (nonseparatingLengthPointMeasure T X,planarLengthPointMeasure H X 1 (by norm_num) 2))
        Q (fun ξ => compactClusterSuperposition F D ε R (twoColorDecode ξ)) := by
  obtain ⟨Q,hQ,hweak⟩ := critical_mixed_poisson_pair_of_short_intersections T MI RG n c hc hn hshort
  refine ⟨Q,hQ,?_⟩
  intro ε R hε
  apply lawConverges_compactClusterSuperposition_of_twoColor_poisson F B C D
    (fun g => wpProbability G g (n g))
    (fun g X => (nonseparatingLengthPointMeasure T X,planarLengthPointMeasure H X 1 (by norm_num) 2))
    nonseparatingLengthIntensity (criticalPantsLengthIntensity c) Q hQ
    (WP.Spectral.wpProbability_eventually_probability P G n
      ((surviving_critical_cusps_tendsto n c hc hn).eventually_ge_atTop 1))
    _ hweak ε R hε
  filter_upwards [] with g
  exact critical_parent_pair_aemeasurable T MI g (n g)

end WP.Critical.PantsCluster
