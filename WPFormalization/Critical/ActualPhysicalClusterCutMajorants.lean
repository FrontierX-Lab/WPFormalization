import WPFormalization.Critical.ActualPhysicalClusterProbabilityComparison
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

def physicalSpectrumCutBadSet {g n : ℕ} (L : ℝ≥0) :
    Set (G.Moduli g n (fun _ => 0)) :=
  physicalSpectrumComparisonBadSet T L
    (fun X=>nonsimpleCutMajorant T X L)
    (fun X=>intersectingCutMajorant T X 2 (2*(L:ℝ)))

include SC

/- All Borel/mean inputs are supplied by actual finite cut-catalog producers.
Only the two pointwise recording dominations remain ordinary internal premises.
They are not classical fields and not a completed G3 or Theorem 14.6. -/
lemma critical_actual_physical_prefix_comparison_of_cut_domination
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
    (MI : MirzakhaniIntegration G H T)
    (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (hnsdom : ∀L : ℝ≥0,∀ᶠg in atTop,∀X : G.Moduli g (n g) (fun _ => 0),
      nonsimpleNonPantsCount A S X L ≤ nonsimpleCutMajorant T X L)
    (hintdom : ∀L : ℝ≥0,∀ᶠg in atTop,∀X : G.Moduli g (n g) (fun _ => 0),
      allShortIntersectingSimpleTupleCount T X 2 (2*(L:ℝ)) ≤
        intersectingCutMajorant T X 2 (2*(L:ℝ))) :
    (∀L : ℝ≥0,∀ᶠg in atTop,MeasurableSet
      (physicalSpectrumCutBadSet T (g:=g) (n:=n g) L)) ∧
    (∀L : ℝ≥0,∀ᶠg in atTop,∀X : G.Moduli g (n g) (fun _ => 0),
      X∉physicalSpectrumCutBadSet T L →
      (physicalPrimitiveLengthPointMeasure H X).toMeasure.restrict (Iic L)=
        ((nonseparatingLengthPointMeasure T X).toMeasure +
          clusterMeasure F (planarLengthPointMeasure H X 1 (by norm_num) 2).toMeasure).restrict (Iic L)) ∧
    (∀L : ℝ≥0,Tendsto (fun g => (wpProbability G g (n g)).real
      (physicalSpectrumCutBadSet T L)) atTop (𝓝 0)) := by
  apply critical_actual_physical_prefix_comparison_of_majorants A T AC Cuts S SC
    F D U BC LS J PC PP FB FL FP FS MI n c hc hn
    (fun L _ X=>nonsimpleCutMajorant T X L)
    (fun L _ X=>intersectingCutMajorant T X 2 (2*(L:ℝ)))
  · intro L
    exact Eventually.of_forall (fun _=>nonsimpleCutMajorant_measurable T MI L)
  · intro L
    exact Eventually.of_forall (fun _=>intersectingCutMajorant_measurable T MI 2 (2*(L:ℝ)))
  · exact hnsdom
  · exact hintdom
  · intro L
    exact critical_nonsimpleCutMajorant_tendsto_zero T MI L L.2 n c hc hn
  · intro L
    exact critical_intersectingCutMajorant_tendsto_zero T MI 2 (2*(L:ℝ))
      (by positivity) n c hc hn

end WP.Critical.PantsCluster
