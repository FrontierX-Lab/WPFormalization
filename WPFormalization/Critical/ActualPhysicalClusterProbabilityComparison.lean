import WPFormalization.Critical.ActualPhysicalClusterGoodEvent
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

include SC

/- Internal probability assembly. The only unfinished paper-specific inputs are
actual measurable G3 majorants and their expectation bounds. The geometric
prefix identity is produced above, rather than added as a premise. -/
lemma critical_actual_physical_prefix_comparison_of_majorants
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
    (Mns Mint : (L : ℝ≥0) → (g : ℕ) → G.Moduli g (n g) (fun _ => 0) → ℝ≥0∞)
    (hns : ∀L : ℝ≥0,∀ᶠg in atTop,Measurable (Mns L g))
    (hint : ∀L : ℝ≥0,∀ᶠg in atTop,Measurable (Mint L g))
    (hnsdom : ∀L : ℝ≥0,∀ᶠg in atTop,∀X,nonsimpleNonPantsCount A S X L ≤ Mns L g X)
    (hintdom : ∀L : ℝ≥0,∀ᶠg in atTop,∀X,
      allShortIntersectingSimpleTupleCount T X 2 (2*(L:ℝ)) ≤ Mint L g X)
    (hnsmean : ∀L : ℝ≥0,Tendsto (fun g => ∫⁻X,Mns L g X ∂wpProbability G g (n g)) atTop (𝓝 0))
    (hintmean : ∀L : ℝ≥0,Tendsto (fun g => ∫⁻X,Mint L g X ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    (∀L : ℝ≥0,∀ᶠg in atTop,MeasurableSet (physicalSpectrumComparisonBadSet T L (Mns L g) (Mint L g))) ∧
    (∀L : ℝ≥0,∀ᶠg in atTop,∀X,X∉physicalSpectrumComparisonBadSet T L (Mns L g) (Mint L g) →
      (physicalPrimitiveLengthPointMeasure H X).toMeasure.restrict (Iic L)=
        ((nonseparatingLengthPointMeasure T X).toMeasure +
          clusterMeasure F (planarLengthPointMeasure H X 1 (by norm_num) 2).toMeasure).restrict (Iic L)) ∧
    (∀L : ℝ≥0,Tendsto (fun g => (wpProbability G g (n g)).real
      (physicalSpectrumComparisonBadSet T L (Mns L g) (Mint L g))) atTop (𝓝 0)) := by
  refine ⟨?_,?_,?_⟩
  · intro L
    filter_upwards [hns L,hint L,eventually_ge_atTop (1:ℕ)] with g hg hi hg1
    exact physicalSpectrumComparisonBadSet_measurable T L MI hg1 hg hi
  · intro L
    filter_upwards [hnsdom L,hintdom L,eventually_ge_atTop (2:ℕ)] with g hg hi hg2 X hoff
    exact actual_physical_cluster_prefix_of_good_geometry A T AC Cuts S SC
      F D U BC LS J PC PP FB FL FP FS hg2 L X
      (physicalSpectrumGeometryGood_of_off_bad A T S L hg hi X hoff)
  · intro L
    exact critical_physicalSpectrumComparisonBadSet_probability_real_tendsto_zero
      T L MI n c hc hn (Mns L) (Mint L) (hns L) (hint L) (hnsmean L) (hintmean L)

end WP.Critical.PantsCluster
