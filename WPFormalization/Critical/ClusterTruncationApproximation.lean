import WPFormalization.Critical.ClusterFiniteWaistMapping
import Mathlib.MeasureTheory.Integral.DominatedConvergence
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter WP.Probability
open scoped ENNReal NNReal Topology CompactlySupported
variable (F : Family.{u,v})

lemma waistTruncatedPairing_tendsto (f : C_c(ℝ≥0,ℝ)) (ε R : ℕ → ℝ≥0)
    (hε : Tendsto ε atTop (𝓝 0)) (hR : Tendsto R atTop atTop) (s : ℝ≥0) :
    Tendsto (fun j => waistTruncatedPairing F f (ε j) (R j) s) atTop (𝓝 (testPairingNN F f s)) := by
  by_cases hs : 0<s
  · have hlo := hε.eventually_lt_const hs
    have hhi : ∀ᶠj in atTop,s≤R j := hR.eventually (eventually_ge_atTop s)
    apply tendsto_const_nhds.congr'
    filter_upwards [hlo,hhi] with j hjlo hjhi
    exact (Set.indicator_of_mem (show s∈Icc (ε j) (R j) from ⟨hjlo.le,hjhi⟩)
      (testPairingNN F f)).symm
  · have hz : s=0 := le_antisymm (le_of_not_gt hs) (by positivity)
    subst s
    have he : (fun j => waistTruncatedPairing F f (ε j) (R j) 0)=fun _ => (0:ℝ) := by
      funext j
      by_cases hm : (0:ℝ≥0)∈Icc (ε j) (R j)
      · simp [waistTruncatedPairing,Set.indicator_of_mem hm,testPairingNN_zero]
      · simp [waistTruncatedPairing,Set.indicator_of_notMem hm]
    rw [he]
    simpa only [testPairingNN_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

lemma compactWaistClusterPointMeasure_tendsto (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (ξ : PointMeasure ℝ≥0) (ε R : ℕ → ℝ≥0)
    (hε : Tendsto ε atTop (𝓝 0)) (hR : Tendsto R atTop atTop) :
    Tendsto (fun j => compactWaistClusterPointMeasure F D ξ (waistWindow (ε j) (R j))) atTop
      (𝓝 (clusterPointMeasure F D hproper ξ)) := by
  change Tendsto _ atTop (@nhds _ (TopologicalSpace.induced _ _) _)
  rw [nhds_induced,tendsto_comap_iff]
  apply tendsto_pi_nhds.mpr
  intro f
  change Tendsto (fun j => ∫x,f x ∂(compactWaistClusterPointMeasure F D ξ
    (waistWindow (ε j) (R j))).toMeasure) atTop
      (𝓝 (∫x,f x ∂(clusterPointMeasure F D hproper ξ).toMeasure))
  simp_rw [compactWaistClusterPointMeasure_integral_truncatedPairing,
    clusterPointMeasure_integral]
  apply tendsto_integral_of_dominated_convergence (fun s => ‖testPairingNN F f s‖)
  · intro j
    exact (waistTruncatedPairing_measurable F D f (ε j) (R j)).aestronglyMeasurable
  · exact (testPairingNN_integrable_signed_of_prefix_cutoff F D hproper f ξ.toMeasure).norm
  · intro j
    apply Eventually.of_forall
    intro s
    by_cases hs : s∈Icc (ε j) (R j)
    · simp only [waistTruncatedPairing,Set.indicator_of_mem hs,le_refl]
    · simp only [waistTruncatedPairing,Set.indicator_of_notMem hs,norm_zero]
      exact norm_nonneg _
  · exact Eventually.of_forall (waistTruncatedPairing_tendsto F f ε R hε hR)

lemma compactClusterSuperposition_tendsto (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0) (ε R : ℕ → ℝ≥0)
    (hε : Tendsto ε atTop (𝓝 0)) (hR : Tendsto R atTop atTop) :
    Tendsto (fun j => compactClusterSuperposition F D (ε j) (R j) p) atTop
      (𝓝 (clusterSuperposition F D hproper p)) := by
  exact pointMeasureAdd_continuous.continuousAt.tendsto.comp
    (tendsto_const_nhds.prodMk_nhds (compactWaistClusterPointMeasure_tendsto F D hproper p.2 ε R hε hR))

theorem lawConverges_compactClusterSuperposition_to_full (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (Q : Measure (PointMeasure ℝ≥0 × PointMeasure ℝ≥0)) [IsProbabilityMeasure Q]
    (ε R : ℕ → ℝ≥0) (hε : Tendsto ε atTop (𝓝 0)) (hR : Tendsto R atTop atTop) :
    LawConverges (fun _ => Q) (fun j => compactClusterSuperposition F D (ε j) (R j))
      Q (clusterSuperposition F D hproper) := by
  intro f
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro j
    exact (f.continuous.measurable.comp
      (compactClusterSuperposition_measurable F D (ε j) (R j))).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact Eventually.of_forall (fun p => f.norm_coe_le_norm _)
  · exact Eventually.of_forall (fun p => f.continuous.continuousAt.tendsto.comp
      (compactClusterSuperposition_tendsto F D hproper p ε R hε hR))

end WP.Critical.PantsCluster
