import WPFormalization.Critical.ComplexShortConfigurationsAssembly
import WPFormalization.Critical.ComplexShortConfigurationsFullStatement
import WPFormalization.Critical.ShortConfigurationRecordingIntersectingMajorant
import VersoBlueprint.Attribute

/-! Whole original G.3, with its literal complement-filling count and the
stronger chosen-support version. Every recording and rate obligation is
proved locally; the parameters are independently sourced classical geometry.
The two actual measurable-majorant certificates remain in each conclusion. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical
open Set Finset Filter WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortSupportingPieceGeometry WP.External.ShortSupportingConstructionGeometry
open WP.External.ShortFundamentalGroupGeometry WP.External.ShortRegularNeighborhoodGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortActualCutRealizationGeometry
open WP.External.ShortBorderedLoopGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortTupleRecordingGeometry WP.External.ShortFullFillingGeometry
open WP.Critical.ShortConfiguration
open scoped Classical ENNReal Topology
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  (A:AmbientRealization H) (T:MulticurveTopology.{u,v,w,z} G H)
  (AC:AmbientCurveCompatibility A T)

@[blueprint "lem:critical-complex"]
theorem complex_short_configurations
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
    (MI : MirzakhaniIntegration G H T) (c : ℝ) (hc : 0 < c) :
    FullComplexShortConfigurationsConclusion A T c ∧
      ComplexShortConfigurationsConclusion A T S c := by
  have hdom := actual_intersecting_cut_domination A T AC Cuts SC SP FG C LS M J PC BC BLS PP
  have hs := complexShortConfigurationsConclusion_of_intersecting_cut_domination
    A T AC S Cuts SCut MI c hc hdom
  exact ⟨fullComplexShortConfigurationsConclusion_of_support_conclusion A T AC S HF c hs, hs⟩

end WP.Critical
