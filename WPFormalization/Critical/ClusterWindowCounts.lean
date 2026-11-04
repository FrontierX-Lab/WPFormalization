import WPFormalization.Critical.ClusterCanonicalMeasures
import WPFormalization.External.PoissonIntegralMoments

/-! Canonical cluster window counts and their finite moments. -/

noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter WP.Probability
open scoped ENNReal NNReal Topology Classical
variable (F : Family.{u, v})

/-- The actual full primitive pants count m_L; zero at the excluded parent 0. -/
def windowMultiplicity (L : ℝ≥0) (s : ℝ≥0) : ℝ :=
  if hs : 0 < s then (measure F ⟨s, by exact_mod_cast hs⟩ (Iic L)).toReal else 0

lemma windowMultiplicity_pos (L s : ℝ≥0) (hs : 0 < s) :
    windowMultiplicity F L s = (measure F ⟨s, by exact_mod_cast hs⟩ (Iic L)).toReal := by
  simp [windowMultiplicity, hs]

lemma windowMultiplicity_nat (L s : ℝ≥0) :
    ∃ n : ℕ, windowMultiplicity F L s = n := by
  by_cases hs : 0 < s
  · rw [windowMultiplicity_pos F L s hs, measure_Iic]
    exact ⟨_, ENNReal.toReal_natCast _⟩
  · exact ⟨0, by simp [windowMultiplicity, hs]⟩

lemma windowMultiplicity_nonneg (L s : ℝ≥0) : 0 ≤ windowMultiplicity F L s := by
  obtain ⟨n, hn⟩ := windowMultiplicity_nat F L s
  rw [hn]; positivity

lemma windowMultiplicity_measurable (D : DeformationClassics F) (L : ℝ≥0) :
    Measurable (windowMultiplicity F L) := by
  have hm : Measurable (fun s => PoissonCluster.indexedKernelMeasure
      (markedLengthNN F) s (Iic L)) := by
    simp only [PoissonCluster.indexedKernelMeasure, Measure.sum_apply _ measurableSet_Iic]
    apply Measurable.tsum
    intro γ
    simp only [Measure.dirac_apply' _ measurableSet_Iic]
    exact Measurable.ite (measurableSet_Iic.preimage (markedLengthNN_measurable F D γ))
      measurable_const measurable_const
  have he : windowMultiplicity F L = (Ioi (0 : ℝ≥0)).indicator
      (fun s => (PoissonCluster.indexedKernelMeasure (markedLengthNN F) s (Iic L)).toReal) := by
    funext s
    by_cases hs : 0 < s
    · simp [windowMultiplicity, hs, indexedKernelMeasure_markedLengthNN_pos]
    · simp [windowMultiplicity, Set.indicator, hs]
  rw [he]
  exact hm.ennreal_toReal.indicator measurableSet_Ioi

lemma windowMultiplicity_bound (L : ℝ≥0) :
    ∃ C : ℝ, ∀ s, ‖windowMultiplicity F L s‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := cluster_prefix_uniform_bound F L
  refine ⟨C, fun s => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (windowMultiplicity_nonneg F L s)]
  by_cases hs : 0 < s
  · rw [windowMultiplicity_pos F L s hs]; exact h _
  · simp [windowMultiplicity, hs, hC.le]

lemma windowMultiplicity_support
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)
    (L : ℝ≥0) : Function.support (windowMultiplicity F L) ⊆ Iic (2*L) := by
  intro s hs
  by_contra hlarge
  have hlt : 2*L < s := lt_of_not_ge hlarge
  have hpos : 0 < s := lt_of_le_of_lt (by positivity) hlt
  have hz := hproper ⟨s, by exact_mod_cast hpos⟩ L (by exact_mod_cast hlt)
  exact hs (by simp [windowMultiplicity, hpos, hz])

lemma windowMultiplicity_integrable (D : DeformationClassics F)
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)
    (L : ℝ≥0) (μ : Measure ℝ≥0) [IsLocallyFiniteMeasure μ] :
    Integrable (windowMultiplicity F L) μ := by
  obtain ⟨C,hC⟩ := windowMultiplicity_bound F L
  apply (integrableOn_iff_integrable_of_support_subset
    (windowMultiplicity_support F hproper L)).mp
  exact Measure.integrableOn_of_bounded
    (PoissonCluster.isCompact_nnreal_prefix _).measure_lt_top.ne
    (windowMultiplicity_measurable F D L).aestronglyMeasurable (Eventually.of_forall hC)

lemma clusterMeasure_prefix_integral (D : DeformationClassics F)
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)
    (L : ℝ≥0) (ξ : PointMeasure ℝ≥0) :
    (clusterMeasure F ξ.toMeasure (Iic L)).toReal =
      ∫ s, windowMultiplicity F L s ∂ξ.toMeasure := by
  rw [clusterMeasure, PoissonCluster.indexedClusterMeasure_apply _
    (markedLengthNN_measurable F D) _ _ measurableSet_Iic,
    ← lintegral_indicator measurableSet_Ioi]
  have he : (Ioi (0 : ℝ≥0)).indicator
      (fun s => PoissonCluster.indexedKernelMeasure (markedLengthNN F) s (Iic L)) =
      fun s => ENNReal.ofReal (windowMultiplicity F L s) := by
    funext s
    by_cases hs : 0 < s
    · simp only [Set.indicator_of_mem (show s ∈ Ioi (0 : ℝ≥0) from hs), indexedKernelMeasure_markedLengthNN_pos F s hs,
        windowMultiplicity_pos F L s hs]
      rw [measure_Iic]
      simp
    · simp [Set.indicator, Set.mem_Ioi, windowMultiplicity, hs]
  rw [he]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (windowMultiplicity_nonneg F L))
    (windowMultiplicity_measurable F D L).aestronglyMeasurable).symm

/-- Real-valued window count, without any truncation of multiplicities. -/
def prefixCount (L : ℝ≥0) (ξ : PointMeasure ℝ≥0) : ℝ := (ξ.toMeasure (Iic L)).toReal

lemma prefixCount_measurable (L : ℝ≥0) : Measurable (prefixCount L) :=
  (PoissonCluster.pointMeasure_eval_measurable _ measurableSet_Iic
    (by rw [closure_Iic]; exact PoissonCluster.isCompact_nnreal_prefix L)).ennreal_toReal

lemma prefixCount_eq_integral (L : ℝ≥0) (ξ : PointMeasure ℝ≥0) :
    prefixCount L ξ = ∫ s, (Iic L).indicator (fun _ => (1 : ℝ)) s ∂ξ.toMeasure := by
  simp [prefixCount, integral_indicator measurableSet_Iic, measureReal_def]

lemma clusterSuperposition_prefixCount (D : DeformationClassics F)
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)
    (L : ℝ≥0) (p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0) :
    prefixCount L (clusterSuperposition F D hproper p) =
      prefixCount L p.1 + ∫ s, windowMultiplicity F L s ∂p.2.toMeasure := by
  change (p.1.toMeasure (Iic L) + (clusterPointMeasure F D hproper p.2).toMeasure (Iic L)).toReal = _
  rw [ENNReal.toReal_add (PoissonCluster.isCompact_nnreal_prefix L).measure_lt_top.ne
    (PoissonCluster.isCompact_nnreal_prefix L).measure_lt_top.ne]
  rw [clusterPointMeasure_toMeasure, clusterMeasure_prefix_integral F D hproper]
  rfl
end WP.Critical.PantsCluster
