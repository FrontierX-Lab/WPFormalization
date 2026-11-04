import WPFormalization.Critical.ActualPantsCatalogPartition
import WPFormalization.Critical.PhysicalPantsClusterPrefix

/- INTERNAL actual ambient/canonical-prefix comparison. The only unproved
paper-specific geometric premise here is the explicitly named short nonsimple
coverage, to be supplied on the genuine G3 good event. No new classical
spectrum identification or stochastic conclusion is assumed. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open WP.External WP.External.PantsCluster WP.RandomGeometry
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortBorderedLoopGeometry WP.External.ShortLoopStraighteningGeometry
open WP.External.PlanarJordanGeometry WP.External.PlanarRegionGeometry
open WP.External.ShortBorderedPeripheralGeometry WP.External.ShortBorderedSingleCurveGeometry
open WP.Probability MeasureTheory Set
open scoped ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G} (A : AmbientRealization H)
  (T : MulticurveTopology.{u,v,w,z} G H) {g n : ℕ}
  (X : G.Moduli g n (fun _ => 0)) (K : ℝ≥0)
  (o : T.Orbit g n (H.shortPlanar X 2 K).card)
  (ho : T.orbitMem o X (physicalPantsWaistTuple H X K))
  (C : CutComponentRealization A T o X (physicalPantsWaistTuple H X K) ho)

lemma actual_physical_cluster_prefix_of_nonsimple_coverage
    (AC : AmbientCurveCompatibility A T)
    (F : Family.{u,w}) (D : DeformationClassics F) (U : UniquenessClassics F)
    (hg : 1≤g)
    (leaf : Fin (H.shortPlanar X 2 K).card → Fin (T.cut o).components)
    (hleaf : ∀e,PantsLeafData (T.cut o) e (leaf e))
    (hp : ∀e,HasPantsTopology (C.piece (leaf e)).model)
    (hb : ∀e,(C.piece (leaf e)).model.boundaries=1)
    (CB : ∀e,PrimitiveBoundaryClassics (C.piece (leaf e)).model (C.piece (leaf e)).boundary)
    (CL : ∀e,BorderedLoopStraighteningClassics (C.piece (leaf e)).model (C.piece (leaf e)).boundary)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (CP : ∀e,BorderedPeripheralClassics (C.piece (leaf e)).model (C.piece (leaf e)).boundary)
    (j : ∀e,Fin (C.piece (leaf e)).model.boundaries)
    (FB : ∀s,PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (FL : ∀s,BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (FP : ∀s,BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀s,BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (L : ℝ≥0) (hK : 2*L≤K)
    (hgood : ¬HasShortSeparatingNonPants T L X)
    (hnonsimple : ∀γ : H.Primitive g n X,¬H.simple γ → H.length γ≤L →
      ∃e,actualPiecePrimitivePredicate A X (C.piece (leaf e)) γ) :
    (physicalPrimitiveLengthPointMeasure H X).toMeasure.restrict (Iic L)=
      ((nonseparatingLengthPointMeasure T X).toMeasure +
        clusterMeasure F (planarLengthPointMeasure H X 1 (by norm_num) 2).toMeasure).restrict (Iic L) := by
  have hκplanar (e : Fin (H.shortPlanar X 2 K).card) :
      ∃S : Finset (Fin n),H.planarSide (physicalPantsWaistTuple H X K e)=some S := by
    obtain ⟨_,S,hS,_⟩ := (H.mem_shortPlanar X 2 K _).mp
      (physicalPantsWaistTuple_mem H X K e)
    exact ⟨S,hS⟩
  have hcomplete : ∀γ : H.Primitive g n X,γ∈H.shortPlanar X 2 K →
      ∃e,physicalPantsWaistTuple H X K e=γ := by
    intro γ hγ
    exact (physicalPantsWaistTuple_complete H X K γ).mp hγ
  have hLK : (L:ℝ)≤(K:ℝ) := by exact_mod_cast (show L≤K by nlinarith [L.2])
  have hdet := actual_pants_spectrum_of_nonsimple_coverage A T AC X C F U hg hκplanar
    leaf hleaf hp hb CB CL J PC CP j L K hLK hcomplete hgood hnonsimple
  have hpref := physicalPantsCluster_prefix_eq_tuple F D H X FB FL J PC FP SC L K hK
  rw [Measure.restrict_add] at hdet ⊢
  rw [hpref]
  exact hdet

end WP.Critical.PantsCluster
