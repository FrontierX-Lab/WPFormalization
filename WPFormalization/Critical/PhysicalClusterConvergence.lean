import WPFormalization.Critical.PhysicalClusterStatement
import WPFormalization.Critical.ClusterCriticalModelLaw
import WPFormalization.Probability.PointMeasurePrefixLawTransfer

/- Internal assembly only. G3 hshort and the actual off-bad prefix comparison
remain explicit ordinary inputs until their local geometric producers are
installed. These are not classical fields, and this is not the final labeled
proof of original Theorem 14.6. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd u v
namespace WP.Critical.PantsCluster
open WP.External WP.External.PantsCluster WP.RandomGeometry WP.Probability MeasureTheory Filter Set
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortComplementaryRegionGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortBorderedSingleCurveGeometry
open scoped NNReal ENNReal Topology CompactlySupported
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)

include MI RG in
lemma critical_physicalClusterLimit_of_short_intersections_and_prefix_comparison
    (F : Family.{u,v}) (D : DeformationClassics F)
    (BC : ∀ s, PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : ∀ s, BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀ s, BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀ s, BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,bb,0})
    (I : WP.External.TwoColorPoissonRestrictionIndependence)
    (LC : WP.External.PointMeasureLaplaceConvergence.{bb,0})
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c))
    (hshort : ∀ t : ℕ, 2 ≤ t → ∀ L : ℝ, 0 ≤ L → Tendsto
      (fun g => ∫⁻ X, allShortIntersectingSimpleTupleCount T X t L
        ∂wpProbability G g (n g)) atTop (𝓝 0))
    (A : (L : ℝ≥0) → (g : ℕ) → Set (G.Moduli g (n g) (fun _ => 0)))
    (hA : ∀ L, ∀ᶠ g in atTop, MeasurableSet (A L g))
    (hprefix : ∀ L, ∀ᶠ g in atTop, ∀ X, X ∉ A L g →
      (physicalPrimitiveLengthPointMeasure H X).toMeasure.restrict (Iic L) =
        ((nonseparatingLengthPointMeasure T X).toMeasure +
          clusterMeasure F (planarLengthPointMeasure H X 1 (by norm_num) 2).toMeasure).restrict (Iic L))
    (hbad : ∀ L, Tendsto (fun g => (wpProbability G g (n g)).real (A L g)) atTop (𝓝 0)) :
    CriticalPhysicalClusterLimit H F D BC LS J PC PP SC n c := by
  obtain ⟨QN,QP,hN,hP,hmodel,_⟩ := critical_canonicalClusterModelLaw_of_short_intersections
    T MI RG F D BC LS J PC PP SC B C I n c hc hn hshort
  refine ⟨QN,QP,hN,hP,?_,?_⟩
  · apply lawConverges_of_prefix_eq_off_bad_events LC
      (fun g => wpProbability G g (n g))
      (fun _ X => physicalPrimitiveLengthPointMeasure H X)
      (fun _ X => clusterSuperposition F D (canonical_prefix_cutoff F BC LS J PC PP SC)
        (nonseparatingLengthPointMeasure T X,planarLengthPointMeasure H X 1 (by norm_num) 2))
      (canonicalClusterSuperpositionLaw F D BC LS J PC PP SC QN QP) id
      (WP.Spectral.wpProbability_eventually_probability P G n
        ((surviving_critical_cusps_tendsto n c hc hn).eventually_ge_atTop 1))
      _ _ measurable_id.aemeasurable A hA _ hbad hmodel
    · filter_upwards [] with g
      exact physicalPrimitiveLengthPointMeasure_aemeasurable H (wpProbability G g (n g))
    · filter_upwards [] with g
      exact (clusterSuperposition_measurable F D (canonical_prefix_cutoff F BC LS J PC PP SC)).comp_aemeasurable
        (critical_parent_pair_aemeasurable T MI g (n g))
    · intro L
      filter_upwards [hprefix L] with g hg X hX
      exact hg X hX
  · intro f hf
    exact canonicalClusterSuperpositionLaw_laplace F D BC LS J PC PP SC
      nonseparatingLengthIntensity (criticalPantsLengthIntensity c) QN QP hN hP f hf

lemma CriticalPhysicalClusterLimit.laplace_expectations
    (F : Family.{u,v}) (D : DeformationClassics F)
    (BC : ∀ s, PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : ∀ s, BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀ s, BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀ s, BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (n : ℕ → ℕ) (c : ℝ)
    (h : CriticalPhysicalClusterLimit H F D BC LS J PC PP SC n c)
    (f : C_c(ℝ≥0,ℝ)) (hf : ∀ x, 0 ≤ f x) :
    Tendsto (fun g => ∫ X, PoissonCluster.laplaceObservable (fun x => f x)
      (physicalPrimitiveLengthPointMeasure H X) ∂wpProbability G g (n g)) atTop
      (𝓝 (Real.exp (-(∫ x, 1 - Real.exp (-f x) ∂nonseparatingLengthIntensity) -
        (∫ s, laplaceCostNN F f s ∂criticalPantsLengthIntensity c)))) := by
  obtain ⟨QN,QP,_,_,hweak,hlap⟩ := h
  have ht := PoissonCluster.lawConverges_laplaceObservable _ _ _ _ hweak f hf
  simp only [id_eq] at ht
  rw [hlap f hf] at ht
  exact ht

end WP.Critical.PantsCluster
