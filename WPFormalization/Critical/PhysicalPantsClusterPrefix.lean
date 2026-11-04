import WPFormalization.Critical.PhysicalPantsClusterSum
import WPFormalization.Critical.ClusterCanonicalMeasures
import WPFormalization.Probability.PoissonClusterPrefixTruncation

/- The actual complete pants parent produces, below physical length L,
exactly the finite canonical clusters indexed by its waists up to 2L.
The proper-prefix bound is discharged by the existing true pants geometry. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace WP.Critical.PantsCluster
open WP.External WP.External.PantsCluster WP.RandomGeometry
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortBorderedLoopGeometry WP.External.ShortLoopStraighteningGeometry
open WP.External.PlanarJordanGeometry WP.External.PlanarRegionGeometry
open WP.External.ShortBorderedPeripheralGeometry WP.External.ShortBorderedSingleCurveGeometry
open WP.Probability MeasureTheory Set
open scoped ENNReal NNReal
variable (F : Family.{u,w}) (D : DeformationClassics F)

include D in
lemma clusterMeasure_restrict_prefix_parent
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val → measure F s (Iic L)=0)
    (ξ : Measure ℝ≥0) (L K : ℝ≥0) (hK : 2*L≤K) :
    (clusterMeasure F ξ).restrict (Iic L)=
      (clusterMeasure F (ξ.restrict (Iic K))).restrict (Iic L) := by
  have hp : ∀s : ℝ≥0,2*L<s →
      PoissonCluster.indexedKernelMeasure (markedLengthNN F) s (Iic L)=0 := by
    intro s hs
    have hs0 : 0<s := lt_of_le_of_lt (by positivity) hs
    rw [indexedKernelMeasure_markedLengthNN_pos F s hs0]
    exact hproper _ L (by exact_mod_cast hs)
  have hi : Icc (0:ℝ≥0) K=Iic K := by ext s;simp
  simpa only [clusterMeasure,hi] using
    PoissonCluster.indexedClusterMeasure_restrict_prefix_eq_compactParent
      (markedLengthNN F) (markedLengthNN_measurable F D) ξ L 0 K hK hp (by simp)

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}
  (X : G.Moduli g n (fun _ => 0))

include D in
lemma physicalPantsCluster_prefix_eq_tuple
    (BC : ∀s,PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : ∀s,BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀s,BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀s,BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (L K : ℝ≥0) (hK : 2*L≤K) :
    (clusterMeasure F (planarLengthPointMeasure H X 1 (by norm_num) 2).toMeasure).restrict (Iic L)=
      (Measure.sum (fun e : Fin (H.shortPlanar X 2 K).card => measure F
        ⟨H.length (physicalPantsWaistTuple H X K e),
          H.length_pos (physicalPantsWaistTuple H X K e)⟩)).restrict (Iic L) := by
  rw [clusterMeasure_restrict_prefix_parent F D
    (canonical_prefix_cutoff F BC LS J PC PP SC) _ L K hK,
    physicalPantsCluster_restrict_parent_eq_tuple F H X D K]

end WP.Critical.PantsCluster
