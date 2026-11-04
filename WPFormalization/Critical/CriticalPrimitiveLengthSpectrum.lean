import WPFormalization.Critical.ComplexShortConfigurations
import WPFormalization.Critical.PhysicalClusterLimitFromConfigurations

/- Final original Theorem 14.6 producer. The actual whole G3 theorem and
actual intersecting-cut recording domination supply every paper input.
There is no comparison, coverage, majorant, moment or G3 premise. The
Blueprint attribute identifies this complete conditional producer. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.PantsCluster
open Set Finset Filter WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortSupportingPieceGeometry WP.External.ShortSupportingConstructionGeometry
open WP.External.ShortFundamentalGroupGeometry WP.External.ShortRegularNeighborhoodGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortActualCutRealizationGeometry
open WP.External.ShortBorderedLoopGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortTupleRecordingGeometry WP.External.ShortFullFillingGeometry
open WP.Critical.ShortConfiguration
open WP.External.PantsCluster WP.External.ShortBorderedSingleCurveGeometry
open scoped Classical ENNReal Topology
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  (A:AmbientRealization H) (T:MulticurveTopology.{u,v,w,z} G H)
  (AC:AmbientCurveCompatibility A T)


@[blueprint "thm:critical-cluster"]
theorem critical_primitive_length_spectrum
    (Cuts:ActualCutRealizationData A T AC.complete_domain)
    (SC:∀g n (X:G.Moduli g n (fun _=>0)),SegmentClassics (A.model g n X))
    (SP:∀g n (X:G.Moduli g n (fun _=>0)),
      SupportingPieceClassics (A.model g n X) (AC.complete_domain g n X))
    (FG:FiniteGraphFundamentalGroupClassics.{u})
    (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (LS:∀g n (X:G.Moduli g n (fun _=>0)),
      LoopStraighteningClassics (A.model g n X) (AC.complete_domain g n X))
    (M:∀g n r (X:G.Moduli g n (fun _=>0)) L (hL:0<L)
      (γ:ShortIntersectingSimpleTuple T X r L),
      TupleRecordingCompanions A AC X γ.val γ.property.1 γ.property.2.1
        (SC g n X) L hL γ.property.2.2.1 (SP g n X) C)
    (J:PlanarJordanClassics) (PC:PlanarRegionClassics)
    (BC:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      PrimitiveBoundaryClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (BLS:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedLoopStraighteningClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (PP:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedPeripheralClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (S : SingleCurvePieceClassics A)
    (SCut : SingleCurveCutCompanionData Cuts S)
    (HF : FullSingleCurveFillingClassics A AC.complete_domain S)
    (F : Family.{u,w}) (D : DeformationClassics F) (U : UniquenessClassics F)
    (FB : ∀ s, PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (FL : ∀ s, BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (FP : ∀ s, BorderedPeripheralClassics (F.model s) (F.boundary s))
    (FS : ∀ s, BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)
    (B : WP.External.CompactBorelVaguePairing)
    (CM : WP.External.AlmostSureContinuousMapping.{0,0,v,0})
    (I : WP.External.TwoColorPoissonRestrictionIndependence)
    (LC : WP.External.PointMeasureLaplaceConvergence.{v,0})
    (c : ℝ) (hc : 0 < c) (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    CriticalPhysicalClusterLimit H F D FB FL J PC FP FS n c := by
  have hG3 := (complex_short_configurations A T AC Cuts SC SP FG C LS M J PC
    BC BLS PP S SCut HF MI c hc).2
  have hdom := actual_intersecting_cut_domination A T AC Cuts SC SP FG C LS M J PC BC BLS PP
  apply critical_physicalClusterLimit_of_complexShortConfigurations_and_intersecting_cut_domination
    A T AC Cuts S SCut F D U
    (fun {g n k} o X κ hκ q => BC g n o X κ hκ q)
    (fun {g n k} o X κ hκ q => BLS g n o X κ hκ q) J PC
    (fun {g n k} o X κ hκ q => PP g n o X κ hκ q)
    FB FL FP FS MI RG B CM I LC c hc hG3 n hn
  intro L
  exact hdom 2 (2*(L:ℝ)) (by positivity) n

end WP.Critical.PantsCluster
