import WPFormalization.Critical.ActualPantsLeafTopology
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

lemma actual_physical_cluster_prefix_of_good_geometry
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
    {g n : ℕ} (hg : 2≤g) (L : ℝ≥0) (X : G.Moduli g n (fun _ => 0))
    (hgood : PhysicalSpectrumGeometryGood A T S L X) :
    (physicalPrimitiveLengthPointMeasure H X).toMeasure.restrict (Iic L)=
      ((nonseparatingLengthPointMeasure T X).toMeasure +
        clusterMeasure F (planarLengthPointMeasure H X 1 (by norm_num) 2).toMeasure).restrict (Iic L) := by
  classical
  have hg1 : 1≤g := by omega
  have hstable : WP.Stable g n := by unfold WP.Stable; omega
  let K : ℝ≥0 := 2*L
  have hK : 2*L≤K := le_rfl
  have hno : ¬HasIntersectingShortPants T (K:ℝ) X := by
    simpa only [K,NNReal.coe_mul,NNReal.coe_ofNat] using hgood.2.1
  obtain ⟨o,ho,_⟩ := physicalPantsWaistTuple_actual_orbit_of_no_bad H X K T hno
  let κ := physicalPantsWaistTuple H X K
  let C := Cuts.cut o X κ ho
  obtain ⟨leaf,hinj,hleaf⟩ := physicalPantsWaistTuple_actual_cut_leaves H T X K hg1 o ho
  have hp : ∀e,HasPantsTopology (C.piece (leaf e)).model := fun e =>
    actual_pants_leaf_hasPantsTopology A T AC Cuts o X κ ho e (leaf e) (hleaf e)
  have hb : ∀e,(C.piece (leaf e)).model.boundaries=1 := fun e =>
    actual_pants_leaf_one_boundary A T AC Cuts o X κ ho e (leaf e) (hleaf e)
  let j : ∀e,Fin (C.piece (leaf e)).model.boundaries := fun e => ⟨0,by rw [hb e]; decide⟩
  apply actual_physical_cluster_prefix_of_nonsimple_coverage A T X K o ho C AC F D U hg1
    leaf hleaf hp hb (fun e=>BC o X κ ho (leaf e)) (fun e=>LS o X κ ho (leaf e))
    J PC (fun e=>PP o X κ ho (leaf e)) j FB FL FP FS L hK hgood.1
  intro γ hns hlen
  have hh := actual_good_single_pants_leaf_coverage A T AC Cuts S SC hstable hg1 X γ hns
    L hlen (hgood.2.2 hstable γ hns hlen)
    (fun o0 δ hδ c=>BC o0 X (fun _ : Fin 1=>δ) hδ c)
    (fun o0 δ hδ c=>LS o0 X (fun _ : Fin 1=>δ) hδ c) J PC
    (fun o0 δ hδ c=>PP o0 X (fun _ : Fin 1=>δ) hδ c)
    o κ ho leaf hleaf
  apply hh
  intro δ hδ hs
  apply (physicalPantsWaistTuple_complete H X K δ).mp
  apply (H.mem_shortPlanar X 2 K δ).mpr
  exact ⟨by simpa only [K,NNReal.coe_mul,NNReal.coe_ofNat] using hδ,hs⟩

end WP.Critical.PantsCluster
