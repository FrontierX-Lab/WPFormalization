import WPFormalization.Critical.ClusterFiniteWaistTests
import WPFormalization.Critical.ClusterPoissonMeasure
import WPFormalization.External.PointMeasureMappingClassics
import WPFormalization.External.PointMeasureDilationTopology
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter WP.Probability TopologicalSpace
open scoped ENNReal NNReal Topology CompactlySupported
variable (F : Family.{u,v})

lemma pointMeasure_continuousAt_of_test_pairings {S : Type*} [TopologicalSpace S]
    (Ξ : S → PointMeasure ℝ≥0) (s : S)
    (h : ∀f : C_c(ℝ≥0,ℝ),ContinuousAt (fun t => ∫x,f x ∂(Ξ t).toMeasure) s) :
    ContinuousAt Ξ s := by
  change Tendsto Ξ (𝓝 s) (@nhds _ (TopologicalSpace.induced _ _) (Ξ s))
  rw [nhds_induced,tendsto_comap_iff]
  exact tendsto_pi_nhds.mpr h

lemma compactWaistClusterPointMeasure_continuousAt
    (B : WP.External.CompactBorelVaguePairing) (D : DeformationClassics F)
    (ε R : ℝ≥0) (hε : 0<ε) (ξ : PointMeasure ℝ≥0)
    (hξε : ξ.toMeasure {ε}=0) (hξR : ξ.toMeasure {R}=0) :
    ContinuousAt (fun η => compactWaistClusterPointMeasure F D η (waistWindow ε R)) ξ := by
  apply pointMeasure_continuousAt_of_test_pairings
  intro f
  have hc := (B (waistTruncatedPairing F f ε R)
    (waistTruncatedPairing_measurable F D f ε R)
    (waistTruncatedPairing_bound F f ε R)
    ⟨Icc ε R,isCompact_Icc,waistTruncatedPairing_support F f ε R⟩).2 ξ
      (waistTruncatedPairing_ae_continuousAt F D f ε R hε ξ.toMeasure hξε hξR)
  simpa only [compactWaistClusterPointMeasure_integral_truncatedPairing] using hc

theorem lawConverges_compactWaistClusterPointMeasure
    (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,w,z})
    (D : DeformationClassics F)
    {Ω : ℕ → Type w} [∀j,MeasurableSpace (Ω j)]
    {Ωlimit : Type z} [MeasurableSpace Ωlimit]
    (μ : (j : ℕ) → Measure (Ω j)) (X : (j : ℕ) → Ω j → PointMeasure ℝ≥0)
    (Q : Measure Ωlimit) [IsProbabilityMeasure Q] (Z : Ωlimit → PointMeasure ℝ≥0)
    (hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hX : ∀ᶠj in atTop,AEMeasurable (X j) (μ j))
    (hZ : AEMeasurable Z Q) (hLaw : LawConverges μ X Q Z)
    (ε R : ℝ≥0) (hε : 0<ε)
    (hzero : ∀ᵐω ∂Q,(Z ω).toMeasure {ε}=0 ∧ (Z ω).toMeasure {R}=0) :
    LawConverges μ
      (fun j ω => compactWaistClusterPointMeasure F D (X j ω) (waistWindow ε R))
      Q (fun ω => compactWaistClusterPointMeasure F D (Z ω) (waistWindow ε R)) := by
  letI : MetrizableSpace (PointMeasure ℝ≥0) :=
    WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable.1
  letI : SecondCountableTopology (PointMeasure ℝ≥0) :=
    WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable.2
  apply C (PointMeasure ℝ≥0) (PointMeasure ℝ≥0) Ω Ωlimit μ X Q Z
    (fun ξ => compactWaistClusterPointMeasure F D ξ (waistWindow ε R)) hprob hX hZ
    (compactWaistClusterPointMeasure_measurable F D (waistWindow ε R)) _ hLaw
  filter_upwards [hzero] with ω hω
  exact compactWaistClusterPointMeasure_continuousAt F B D ε R hε (Z ω) hω.1 hω.2

def compactClusterSuperposition (D : DeformationClassics F) (ε R : ℝ≥0)
    (p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0) : PointMeasure ℝ≥0 :=
  pointMeasureAdd p.1 (compactWaistClusterPointMeasure F D p.2 (waistWindow ε R))

lemma compactClusterSuperposition_continuousAt
    (B : WP.External.CompactBorelVaguePairing) (D : DeformationClassics F)
    (ε R : ℝ≥0) (hε : 0<ε) (p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0)
    (hpε : p.2.toMeasure {ε}=0) (hpR : p.2.toMeasure {R}=0) :
    ContinuousAt (compactClusterSuperposition F D ε R) p := by
  exact pointMeasureAdd_continuous.continuousAt.comp
    (continuousAt_fst.prodMk
      ((compactWaistClusterPointMeasure_continuousAt F B D ε R hε p.2 hpε hpR).comp continuousAt_snd))

lemma compactClusterSuperposition_measurable (D : DeformationClassics F) (ε R : ℝ≥0) :
    Measurable (compactClusterSuperposition F D ε R) := by
  apply PoissonCluster.pointMeasure_measurable_of_prefix_counts
  intro b
  apply PoissonCluster.measurable_pointMeasure_prefix_count
  change Measurable (fun p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0 =>
    p.1.toMeasure (Iic b)+(compactWaistClusterPointMeasure F D p.2 (waistWindow ε R)).toMeasure (Iic b))
  have he := PoissonCluster.pointMeasure_eval_measurable (Iic b) measurableSet_Iic
    (by rw [isClosed_Iic.closure_eq];exact PoissonCluster.isCompact_nnreal_prefix b)
  exact (he.comp measurable_fst).add
    (he.comp ((compactWaistClusterPointMeasure_measurable F D (waistWindow ε R)).comp measurable_snd))

theorem lawConverges_compactClusterSuperposition
    (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,w,z})
    (D : DeformationClassics F)
    {Ω : ℕ → Type w} [∀j,MeasurableSpace (Ω j)]
    {Ωlimit : Type z} [MeasurableSpace Ωlimit]
    (μ : (j : ℕ) → Measure (Ω j))
    (X : (j : ℕ) → Ω j → PointMeasure ℝ≥0 × PointMeasure ℝ≥0)
    (Q : Measure Ωlimit) [IsProbabilityMeasure Q]
    (Z : Ωlimit → PointMeasure ℝ≥0 × PointMeasure ℝ≥0)
    (hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hX : ∀ᶠj in atTop,AEMeasurable (X j) (μ j))
    (hZ : AEMeasurable Z Q) (hLaw : LawConverges μ X Q Z)
    (ε R : ℝ≥0) (hε : 0<ε)
    (hzero : ∀ᵐω ∂Q,(Z ω).2.toMeasure {ε}=0 ∧ (Z ω).2.toMeasure {R}=0) :
    LawConverges μ (fun j ω => compactClusterSuperposition F D ε R (X j ω))
      Q (fun ω => compactClusterSuperposition F D ε R (Z ω)) := by
  letI : MetrizableSpace (PointMeasure ℝ≥0) :=
    WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable.1
  letI : SecondCountableTopology (PointMeasure ℝ≥0) :=
    WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable.2
  apply C (PointMeasure ℝ≥0 × PointMeasure ℝ≥0) (PointMeasure ℝ≥0) Ω Ωlimit μ X Q Z
    (compactClusterSuperposition F D ε R) hprob hX hZ
    (compactClusterSuperposition_measurable F D ε R) _ hLaw
  filter_upwards [hzero] with ω hω
  exact compactClusterSuperposition_continuousAt F B D ε R hε (Z ω) hω.1 hω.2

end WP.Critical.PantsCluster
