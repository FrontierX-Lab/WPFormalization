import WPFormalization.Critical.ClusterMeasurePairings
import WPFormalization.Probability.PoissonClusterMeasurability
import WPFormalization.Probability.PointMeasureAddition
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter WP.Probability
open scoped ENNReal NNReal Topology CompactlySupported
variable (F : Family.{u,v})

lemma clusterPointMeasure_measurable (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0) :
    Measurable (clusterPointMeasure F D hproper) :=
  PoissonCluster.indexedClusterPointMeasure_measurable (markedLengthNN F)
    (markedLengthNN_measurable F D) (cluster_kernel_uniform_bound F) (cluster_kernel_proper F hproper)

lemma compactWaistClusterPointMeasure_measurable (D : DeformationClassics F)
    (W : RelCompactBorelWindow ℝ≥0) :
    Measurable (fun ξ => compactWaistClusterPointMeasure F D ξ W) :=
  PoissonCluster.compactParentClusterPointMeasure_measurable (markedLengthNN F)
    (markedLengthNN_measurable F D) W (cluster_kernel_uniform_bound F)

/- The first parent contains ordinary nonseparating atoms; each atom of the
second parent is replaced by the complete actual primitive pants spectrum. -/
def clusterSuperposition (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0) : PointMeasure ℝ≥0 :=
  pointMeasureAdd p.1 (clusterPointMeasure F D hproper p.2)

lemma clusterSuperposition_measurable (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0) :
    Measurable (clusterSuperposition F D hproper) := by
  apply PoissonCluster.pointMeasure_measurable_of_prefix_counts
  intro b
  apply PoissonCluster.measurable_pointMeasure_prefix_count
  change Measurable (fun p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0 =>
    p.1.toMeasure (Iic b)+(clusterPointMeasure F D hproper p.2).toMeasure (Iic b))
  have he := PoissonCluster.pointMeasure_eval_measurable (Iic b) measurableSet_Iic
    (by rw [isClosed_Iic.closure_eq];exact PoissonCluster.isCompact_nnreal_prefix b)
  exact (he.comp measurable_fst).add
    (he.comp ((clusterPointMeasure_measurable F D hproper).comp measurable_snd))

lemma clusterSuperposition_integral (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0) (f : C_c(ℝ≥0,ℝ)) :
    (∫x,f x ∂(clusterSuperposition F D hproper p).toMeasure)=
      (∫x,f x ∂p.1.toMeasure)+(∫s,testPairingNN F f s ∂p.2.toMeasure) := by
  rw [clusterSuperposition,pointMeasureAdd_integral,clusterPointMeasure_integral]

lemma clusterSuperposition_laplaceObservable (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0) (f : C_c(ℝ≥0,ℝ)) :
    PoissonCluster.laplaceObservable (fun x=>f x) (clusterSuperposition F D hproper p)=
      PoissonCluster.jointLaplaceObservable (fun x=>f x) (testPairingNN F f) p := by
  simp only [PoissonCluster.laplaceObservable,clusterSuperposition_integral,
    PoissonCluster.jointLaplaceObservable,neg_add,sub_eq_add_neg]

def clusterSuperpositionLaw (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0)) : ProbabilityMeasure (PointMeasure ℝ≥0) :=
  ⟨((QN : Measure (PointMeasure ℝ≥0)).prod QP).map (clusterSuperposition F D hproper),
    inferInstance⟩

lemma clusterSuperpositionLaw_toMeasure (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0)) :
    (clusterSuperpositionLaw F D hproper QN QP).toMeasure=
      ((QN : Measure (PointMeasure ℝ≥0)).prod QP).map (clusterSuperposition F D hproper) := rfl

theorem clusterSuperpositionLaw_laplace (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    [IsLocallyFiniteMeasure μ] [Measure.Regular μ]
    (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0))
    (hN : IsPoissonPointProcessLaw ℝ≥0 ν QN) (hP : IsPoissonPointProcessLaw ℝ≥0 μ QP)
    (f : C_c(ℝ≥0,ℝ)) (hf : ∀x,0≤f x) :
    (∫ξ,PoissonCluster.laplaceObservable (fun x=>f x) ξ
      ∂clusterSuperpositionLaw F D hproper QN QP)=
      Real.exp (-(∫x,1-Real.exp (-f x) ∂ν)-(∫s,laplaceCostNN F f s ∂μ)) := by
  rw [clusterSuperpositionLaw_toMeasure,integral_map
    (clusterSuperposition_measurable F D hproper).aemeasurable]
  · simp_rw [clusterSuperposition_laplaceObservable F D hproper]
    exact independent_pants_pairing_laplace_of_prefix_cutoff F D hproper ν μ QN QP hN hP f hf
  · exact (Real.continuous_exp.comp (pointMeasure_vague_test_continuous f).neg).aestronglyMeasurable

end WP.Critical.PantsCluster
