import WPFormalization.Critical.ClusterOverdispersionStatement
import WPFormalization.Critical.ClusterWindowPositive
import VersoBlueprint

/-! Equation (14.22) for the same canonical independent-PPP law as Theorem 14.6. -/
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External MeasureTheory ProbabilityTheory WP.Probability
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortComplementaryRegionGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortBorderedSingleCurveGeometry
open scoped NNReal ENNReal

@[blueprint "eq:cluster-overdispersion"]
theorem critical_cluster_overdispersion
    (F : Family.{u, v}) (D : DeformationClassics F)
    (BC : ∀ s, PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : ∀ s, BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀ s, BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀ s, BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (C : PoissonIntegralMoments) (R : FigureEightClassics F)
    (c : ℝ) (hc : 0 < c) (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0))
    (hN : IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QN)
    (hP : IsPoissonPointProcessLaw ℝ≥0 (criticalPantsLengthIntensity c) QP) :
    ClusterOverdispersionConclusion F c
      (canonicalClusterSuperpositionLaw F D BC LS J PC PP SC QN QP) := by
  let hp := canonical_prefix_cutoff F BC LS J PC PP SC
  have he := clusterWindow_overdispersion F D hp C _ _ QN QP hN hP
  have hpos (L : ℝ≥0) (hL : 2 * Real.arcosh 3 < L) :
      (∫ ξ, prefixCount L ξ ∂clusterSuperpositionLaw F D hp QN QP) <
        variance (prefixCount L) (clusterSuperpositionLaw F D hp QN QP) := by
    have hh := clusterWindow_excess_pos F D R hp c hc L hL
    rw [← he L] at hh
    linarith
  refine ⟨clusterWindow_allMoments F D hp C _ _ QN QP hN hP, he, hpos, ?_⟩
  intro ρ hρ hQ
  let L : ℝ≥0 := ⟨2 * Real.arcosh 3 + 1, by
    have := Real.arcosh_nonneg (x := 3) (by norm_num); linarith⟩
  have hL : 2 * Real.arcosh 3 < (L : ℝ) := by
    change 2 * Real.arcosh 3 < 2 * Real.arcosh 3 + 1
    linarith
  obtain ⟨_,hmean,hvar⟩ := prefixCount_poisson_moments C ρ _ hQ L
  have hh := hpos L hL
  change (∫ ξ, prefixCount L ξ ∂canonicalClusterSuperpositionLaw F D BC LS J PC PP SC QN QP) <
    variance (prefixCount L) (canonicalClusterSuperpositionLaw F D BC LS J PC PP SC QN QP) at hh
  rw [hmean,hvar] at hh
  exact lt_irrefl _ hh
end WP.Critical.PantsCluster
