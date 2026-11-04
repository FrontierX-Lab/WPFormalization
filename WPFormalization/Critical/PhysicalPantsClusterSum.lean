import WPFormalization.Critical.PhysicalPantsWaistMeasure
import WPFormalization.Critical.ClusterMeasure

/- Reindex the actual finite pants parent measure into its complete canonical
cluster spectra. This is deterministic sum/pushforward algebra at physical
lengths, not a probabilistic or geometric comparison assumption. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open WP.External WP.External.PantsCluster WP.RandomGeometry
open WP.Probability MeasureTheory Set
open scoped ENNReal NNReal
variable (F : Family.{u,w})

lemma clusterMeasure_dirac (s : Waist) :
    clusterMeasure F (Measure.dirac (Real.toNNReal s.val))=measure F s := by
  have hs : 0<Real.toNNReal s.val := Real.toNNReal_pos.mpr s.property
  unfold clusterMeasure PoissonCluster.indexedClusterMeasure
  simp only [restrict_dirac,Set.mem_Ioi,hs,ite_true,Measure.map_dirac]
  change PoissonCluster.indexedKernelMeasure (markedLengthNN F) (Real.toNNReal s.val)=_
  rw [indexedKernelMeasure_markedLengthNN_pos F _ hs]
  congr 1
  exact Subtype.ext (Real.coe_toNNReal _ s.property.le)


lemma clusterMeasure_sum (D : DeformationClassics F) {ι : Type z}
    (μ : ι → Measure ℝ≥0) :
    clusterMeasure F (Measure.sum μ)=Measure.sum (fun i => clusterMeasure F (μ i)) := by
  unfold clusterMeasure PoissonCluster.indexedClusterMeasure
  rw [Measure.restrict_sum _ measurableSet_Ioi]
  simp_rw [Measure.map_sum (markedLengthNN_measurable F D _).aemeasurable]
  exact Measure.sum_comm _


lemma clusterMeasure_sum_dirac (D : DeformationClassics F) {ι : Type z}
    (s : ι → Waist) :
    clusterMeasure F (Measure.sum (fun i => Measure.dirac (Real.toNNReal (s i).val)))=
      Measure.sum (fun i => measure F (s i)) := by
  rw [clusterMeasure_sum F D]
  congr 1
  funext i
  exact clusterMeasure_dirac F (s i)


variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}
  (X : G.Moduli g n (fun _ => 0))

lemma physicalPantsCluster_restrict_parent_eq_tuple (D : DeformationClassics F) (K : ℝ≥0) :
    clusterMeasure F ((planarLengthPointMeasure H X 1 (by norm_num) 2).toMeasure.restrict (Iic K))=
      Measure.sum (fun e : Fin (H.shortPlanar X 2 K).card => measure F
        ⟨H.length (physicalPantsWaistTuple H X K e),
          H.length_pos (physicalPantsWaistTuple H X K e)⟩) := by
  rw [physicalPantsWaistMeasure_restrict_eq_tuple]
  exact clusterMeasure_sum_dirac F D
    (fun e : Fin (H.shortPlanar X 2 K).card =>
      ⟨H.length (physicalPantsWaistTuple H X K e),
        H.length_pos (physicalPantsWaistTuple H X K e)⟩)

end WP.Critical.PantsCluster
