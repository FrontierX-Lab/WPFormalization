import WPFormalization.Critical.ClusterWindowCounts

/-! Canonical cluster window counts and their finite moments. -/

noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External MeasureTheory ProbabilityTheory Set Filter WP.Probability
open scoped ENNReal NNReal Topology Classical

lemma prefixCount_poisson_moments (C : PoissonIntegralMoments)
    (μ : Measure ℝ≥0) [IsLocallyFiniteMeasure μ]
    (Q : ProbabilityMeasure (PointMeasure ℝ≥0))
    (hQ : IsPoissonPointProcessLaw ℝ≥0 μ Q) (L : ℝ≥0) :
    (∀ n : ℕ, MemLp (prefixCount L) n Q) ∧
    (∫ ξ, prefixCount L ξ ∂Q) = (μ (Iic L)).toReal ∧
    variance (prefixCount L) Q = (μ (Iic L)).toReal := by
  have hb : ∃ C : ℝ, ∀ s : ℝ≥0, ‖(Iic L).indicator (fun _ => (1 : ℝ)) s‖ ≤ C := by
    refine ⟨1, fun s => ?_⟩
    by_cases hs : s ∈ Iic L <;> simp [Set.indicator, hs]
  have hs : ∃ R : ℝ≥0, Function.support ((Iic L).indicator (fun _ => (1 : ℝ))) ⊆ Iic R :=
    ⟨L, Set.support_indicator_subset⟩
  have h := C.moments μ Q hQ _ (measurable_const.indicator measurableSet_Iic) hb hs
  simp_rw [← prefixCount_eq_integral] at h
  have he : (fun s : ℝ≥0 => ((Iic L).indicator (fun _ => (1 : ℝ)) s)^2) =
      (Iic L).indicator (fun _ => (1 : ℝ)) := by
    funext s; by_cases hs : s ∈ Iic L <;> simp [Set.indicator, hs]
  simpa only [he, integral_indicator measurableSet_Iic, integral_const,
    Measure.restrict_apply_univ, smul_eq_mul, mul_one, measureReal_def] using h

variable (F : Family.{u, v}) (D : DeformationClassics F)
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)

include D hproper in
lemma windowMultiplicity_sq_integrable (L : ℝ≥0) (μ : Measure ℝ≥0)
    [IsLocallyFiniteMeasure μ] : Integrable (fun s => (windowMultiplicity F L s)^2) μ := by
  obtain ⟨C,hC⟩ := windowMultiplicity_bound F L
  apply (integrableOn_iff_integrable_of_support_subset
    (show Function.support (fun s => (windowMultiplicity F L s)^2) ⊆ Iic (2*L) from by
      intro s hs
      exact windowMultiplicity_support F hproper L (by
        intro hz; exact hs (by simp [hz])))).mp
  apply Measure.integrableOn_of_bounded
    (PoissonCluster.isCompact_nnreal_prefix _).measure_lt_top.ne
    ((windowMultiplicity_measurable F D L).pow_const 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro s
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC s) _

lemma clusterWindow_allMoments (C : PoissonIntegralMoments)
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0))
    (hN : IsPoissonPointProcessLaw ℝ≥0 ν QN) (hP : IsPoissonPointProcessLaw ℝ≥0 μ QP)
    (L : ℝ≥0) (n : ℕ) :
    MemLp (prefixCount L) n (clusterSuperpositionLaw F D hproper QN QP) := by
  have hN' := (prefixCount_poisson_moments C ν QN hN L).1 n
  have hP' := (C.moments μ QP hP _ (windowMultiplicity_measurable F D L)
    (windowMultiplicity_bound F L) ⟨2*L, windowMultiplicity_support F hproper L⟩).1 n
  rw [clusterSuperpositionLaw_toMeasure]
  apply (memLp_map_measure_iff (prefixCount_measurable L).aestronglyMeasurable
    (clusterSuperposition_measurable F D hproper).aemeasurable).mpr
  simp only [Function.comp_def, clusterSuperposition_prefixCount]
  exact
    (hN'.comp_fst (QP : Measure (PointMeasure ℝ≥0))).add (hP'.comp_snd (QN : Measure (PointMeasure ℝ≥0)))

lemma clusterWindow_overdispersion (C : PoissonIntegralMoments)
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0))
    (hN : IsPoissonPointProcessLaw ℝ≥0 ν QN) (hP : IsPoissonPointProcessLaw ℝ≥0 μ QP)
    (L : ℝ≥0) :
    variance (prefixCount L) (clusterSuperpositionLaw F D hproper QN QP) -
      (∫ ξ, prefixCount L ξ ∂clusterSuperpositionLaw F D hproper QN QP) =
    ∫ s, windowMultiplicity F L s * (windowMultiplicity F L s - 1) ∂μ := by
  obtain ⟨hNm,hNe,hNv⟩ := prefixCount_poisson_moments C ν QN hN L
  obtain ⟨hPm,hPe,hPv⟩ := C.moments μ QP hP _ (windowMultiplicity_measurable F D L)
    (windowMultiplicity_bound F L) ⟨2*L, windowMultiplicity_support F hproper L⟩
  rw [clusterSuperpositionLaw_toMeasure, variance_map (prefixCount_measurable L).aemeasurable
    (clusterSuperposition_measurable F D hproper).aemeasurable,
    integral_map (clusterSuperposition_measurable F D hproper).aemeasurable
      (prefixCount_measurable L).aestronglyMeasurable]
  simp only [Function.comp_def, clusterSuperposition_prefixCount]
  have hiN : Integrable (fun p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0 => prefixCount L p.1)
      ((QN : Measure (PointMeasure ℝ≥0)).prod QP) :=
    ((hNm 1).integrable (by norm_num)).comp_fst _
  have hiP : Integrable (fun p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0 =>
      ∫ s, windowMultiplicity F L s ∂p.2.toMeasure)
      ((QN : Measure (PointMeasure ℝ≥0)).prod QP) :=
    ((hPm 1).integrable (by norm_num)).comp_snd _
  rw [variance_add_prod (hNm 2) (hPm 2), integral_add hiN hiP,
    integral_fun_fst, integral_fun_snd (fun ξ : PointMeasure ℝ≥0 =>
      ∫ s, windowMultiplicity F L s ∂ξ.toMeasure)]
  simp only [probReal_univ, one_smul, hNe, hNv, hPe, hPv]
  have he : (fun s => windowMultiplicity F L s * (windowMultiplicity F L s - 1)) =
      fun s => (windowMultiplicity F L s)^2 - windowMultiplicity F L s := by
    funext s; ring
  rw [he, integral_sub (windowMultiplicity_sq_integrable F D hproper L μ)
    (windowMultiplicity_integrable F D hproper L μ)]
  ring
end WP.Critical.PantsCluster
