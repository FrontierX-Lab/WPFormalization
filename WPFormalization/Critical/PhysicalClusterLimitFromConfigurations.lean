import WPFormalization.Critical.ActualPhysicalClusterCutComparison
import WPFormalization.Critical.PhysicalClusterConvergence
import WPFormalization.Critical.ComplexShortConfigurationsStatement
import WPFormalization.Critical.ShortConfigurationRecordingNonsimpleMajorant
import WPFormalization.Critical.ShortConfigurationNonsimpleMajorant
import WPFormalization.Critical.ShortConfigurationIntersectingMajorant
import WPFormalization.Critical.PhysicalSpectrumGoodGeometry
import WPFormalization.Critical.PantsClusterSupportCoverage
import WPFormalization.Critical.ActualPhysicalClusterComparison

/- Local genuine geometry assembly. All short primitive curves are assigned
on the actual good event. No coverage or spectrum comparison is an assumption. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open WP.External WP.RandomGeometry WP.External.PantsCluster
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortActualCutRealizationGeometry
open WP.External.ShortBorderedLoopGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortBorderedSingleCurveGeometry
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  (A : AmbientRealization H) (T : MulticurveTopology.{u,v,w,z} G H)
  (AC : AmbientCurveCompatibility A T)
  (Cuts : ActualCutRealizationData A T AC.complete_domain)
  (S : SingleCurvePieceClassics A) (SC : SingleCurveCutCompanionData Cuts S)

open WP.Critical.ShortConfiguration

include SC

/- Internal final-law assembly. G3 is still an ordinary paper premise,
and the actual intersecting-cut domination is supplied separately until its
recording producer is installed. No abstract a.e. certificate is substituted
for the actual Borel cut majorants used by the comparison bad event. -/
lemma critical_physicalClusterLimit_of_complexShortConfigurations_and_intersecting_cut_domination
    (F : Family.{u,w}) (D : DeformationClassics F) (U : UniquenessClassics F)
    (BC : ∀{g n k : ℕ}(o : T.Orbit g n k)(X : G.Moduli g n (fun _ => 0))
      (κ : Fin k → H.Primitive g n X)(hκ : T.orbitMem o X κ)(c : Fin (T.cut o).components),
      PrimitiveBoundaryClassics ((Cuts.cut o X κ hκ).piece c).model
        ((Cuts.cut o X κ hκ).piece c).boundary)
    (LS : ∀{g n k : ℕ}(o : T.Orbit g n k)(X : G.Moduli g n (fun _ => 0))
      (κ : Fin k → H.Primitive g n X)(hκ : T.orbitMem o X κ)(c : Fin (T.cut o).components),
      BorderedLoopStraighteningClassics ((Cuts.cut o X κ hκ).piece c).model
        ((Cuts.cut o X κ hκ).piece c).boundary)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀{g n k : ℕ}(o : T.Orbit g n k)(X : G.Moduli g n (fun _ => 0))
      (κ : Fin k → H.Primitive g n X)(hκ : T.orbitMem o X κ)(c : Fin (T.cut o).components),
      BorderedPeripheralClassics ((Cuts.cut o X κ hκ).piece c).model
        ((Cuts.cut o X κ hκ).piece c).boundary)
    (FB : ∀s,PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (FL : ∀s,BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (FP : ∀s,BorderedPeripheralClassics (F.model s) (F.boundary s))
    (FS : ∀s,BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)
    (B : WP.External.CompactBorelVaguePairing)
    (CM : WP.External.AlmostSureContinuousMapping.{0,0,v,0})
    (I : WP.External.TwoColorPoissonRestrictionIndependence)
    (LC : WP.External.PointMeasureLaplaceConvergence.{v,0})
    (c : ℝ) (hc : 0<c) (hG3 : ComplexShortConfigurationsConclusion A T S c)
    (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (hintdom : ∀L : ℝ≥0,∀ᶠg in atTop,∀X : G.Moduli g (n g) (fun _ => 0),
      allShortIntersectingSimpleTupleCount T X 2 (2*(L:ℝ)) ≤
        intersectingCutMajorant T X 2 (2*(L:ℝ))) :
    CriticalPhysicalClusterLimit H F D FB FL J PC FP FS n c := by
  obtain ⟨hA,hprefix,hbad⟩ :=
    critical_actual_physical_prefix_comparison_of_intersecting_cut_domination
      A T AC Cuts S SC F D U BC LS J PC PP FB FL FP FS MI n c hc hn hintdom
  apply critical_physicalClusterLimit_of_short_intersections_and_prefix_comparison
    T MI RG F D FB FL J PC FP FS B CM I LC n c hc hn _
    (fun L g => physicalSpectrumCutBadSet T (g:=g) (n:=n g) L) hA hprefix hbad
  intro r _ L hL
  exact intersecting_moments_tendsto_zero_of_complexShortConfigurations A T S hG3 n hn r L hL

end WP.Critical.PantsCluster
