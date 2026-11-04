import WPFormalization.Critical.PantsClusterSupportProducer
import WPFormalization.Critical.ClusterPoissonMeasure
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set WP.Probability
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortComplementaryRegionGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortBorderedSingleCurveGeometry
open scoped NNReal ENNReal Topology CompactlySupported
variable (F : Family.{u,v}) (D : DeformationClassics F)
    (BC : ∀s,PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : ∀s,BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀s,BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀s,BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))

/- These canonical consumers discharge the proper-support estimate by the
local actual-pants geometry theorem. No support hypothesis is a field. -/
def canonicalClusterPointMeasure (ξ : PointMeasure ℝ≥0) : PointMeasure ℝ≥0 :=
  clusterPointMeasure F D (canonical_prefix_cutoff F BC LS J PC PP SC) ξ

lemma canonicalClusterPointMeasure_toMeasure (ξ : PointMeasure ℝ≥0) :
    (canonicalClusterPointMeasure F D BC LS J PC PP SC ξ).toMeasure=
      clusterMeasure F ξ.toMeasure := rfl

lemma canonicalClusterPointMeasure_measurable :
    Measurable (canonicalClusterPointMeasure F D BC LS J PC PP SC) :=
  clusterPointMeasure_measurable F D (canonical_prefix_cutoff F BC LS J PC PP SC)

lemma canonicalClusterPointMeasure_integral (ξ : PointMeasure ℝ≥0) (f : C_c(ℝ≥0,ℝ)) :
    (∫x,f x ∂(canonicalClusterPointMeasure F D BC LS J PC PP SC ξ).toMeasure)=
      ∫s,testPairingNN F f s ∂ξ.toMeasure :=
  clusterPointMeasure_integral F D (canonical_prefix_cutoff F BC LS J PC PP SC) ξ f

def canonicalClusterSuperpositionLaw
    (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0)) : ProbabilityMeasure (PointMeasure ℝ≥0) :=
  clusterSuperpositionLaw F D (canonical_prefix_cutoff F BC LS J PC PP SC) QN QP

theorem canonicalClusterSuperpositionLaw_laplace
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    [IsLocallyFiniteMeasure μ] [Measure.Regular μ]
    (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0))
    (hN : IsPoissonPointProcessLaw ℝ≥0 ν QN) (hP : IsPoissonPointProcessLaw ℝ≥0 μ QP)
    (f : C_c(ℝ≥0,ℝ)) (hf : ∀x,0≤f x) :
    (∫ξ,PoissonCluster.laplaceObservable (fun x=>f x) ξ
      ∂canonicalClusterSuperpositionLaw F D BC LS J PC PP SC QN QP)=
      Real.exp (-(∫x,1-Real.exp (-f x) ∂ν)-(∫s,laplaceCostNN F f s ∂μ)) :=
  clusterSuperpositionLaw_laplace F D (canonical_prefix_cutoff F BC LS J PC PP SC)
    ν μ QN QP hN hP f hf

end WP.Critical.PantsCluster
