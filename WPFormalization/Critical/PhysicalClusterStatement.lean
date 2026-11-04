import WPFormalization.Critical.ClusterCanonicalMeasures
import WPFormalization.Critical.PhysicalPrimitivePointMeasure
import WPFormalization.Probability.TwoColorPointMeasuresIntensities

/- Statement-only bundle for original Theorem 14.6. The source is the complete
physical primitive unoriented spectrum. The target is the genuine pushforward
of two independent PPPs, with each pants atom replaced by its complete actual
canonical kernel (waist once, geometric multiplicities retained).
This definition supplies no proof or final Blueprint binding. -/
noncomputable section
universe aa bb cc u v
namespace WP.Critical.PantsCluster
open WP.External WP.External.PantsCluster WP.Probability MeasureTheory Filter Set
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortComplementaryRegionGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortBorderedSingleCurveGeometry
open scoped NNReal Topology CompactlySupported

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}

def CriticalPhysicalClusterLimit (H : HyperbolicCurveGeometry.{aa,bb,cc} G)
    (F : Family.{u,v}) (D : DeformationClassics F)
    (BC : ∀ s, PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : ∀ s, BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀ s, BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀ s, BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (n : ℕ → ℕ) (c : ℝ) : Prop :=
  ∃ QN QP : ProbabilityMeasure (PointMeasure ℝ≥0),
    IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QN ∧
    IsPoissonPointProcessLaw ℝ≥0 (criticalPantsLengthIntensity c) QP ∧
    LawConverges (fun g => wpProbability G g (n g))
      (fun _ X => physicalPrimitiveLengthPointMeasure H X)
      (canonicalClusterSuperpositionLaw F D BC LS J PC PP SC QN QP) id ∧
    ∀ f : C_c(ℝ≥0,ℝ), (∀ x, 0 ≤ f x) →
      (∫ ξ, PoissonCluster.laplaceObservable (fun x => f x) ξ
        ∂canonicalClusterSuperpositionLaw F D BC LS J PC PP SC QN QP) =
        Real.exp (-(∫ x, 1 - Real.exp (-f x) ∂nonseparatingLengthIntensity) -
          (∫ s, laplaceCostNN F f s ∂criticalPantsLengthIntensity c))

end WP.Critical.PantsCluster
