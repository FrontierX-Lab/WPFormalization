import WPFormalization.Critical.ComplexShortConfigurations
import WPFormalization.Critical.JointPoissonLimit

/- Final whole-paper G.4 producer. All new G3 recording obligations are
proved by the actual whole G3 theorem; only reviewed classical parameters
remain. The original Blueprint attribute is added after independent review. -/
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


@[blueprint "lem:critical-skeleton"]
theorem joint_nonseparating_pants_poisson_limit
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
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)
    (I : WP.External.TwoColorPoissonRestrictionIndependence)
    (c : ℝ) (hc : 0 < c) (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    CriticalJointPoissonLimit T n c := by
  have hG3 := (complex_short_configurations A T AC Cuts SC SP FG C LS M J PC
    BC BLS PP S SCut HF MI c hc).2
  exact critical_jointPoissonLimit_of_complexShortConfigurations T A S MI RG I c hc hG3 n hn

end WP.Critical
