import WPFormalization.Critical.ClusterFiniteWaistMapping
import WPFormalization.Probability.PoissonNullWindows
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter WP.Probability
open scoped ENNReal NNReal Topology CompactlySupported
variable (F : Family.{u,v})

def compactClusterSuperpositionLaw (D : DeformationClassics F) (ε R : ℝ≥0)
    (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0)) : ProbabilityMeasure (PointMeasure ℝ≥0) :=
  ⟨((QN : Measure (PointMeasure ℝ≥0)).prod QP).map (compactClusterSuperposition F D ε R),
    inferInstance⟩

lemma compactClusterSuperpositionLaw_toMeasure (D : DeformationClassics F) (ε R : ℝ≥0)
    (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0)) :
    (compactClusterSuperpositionLaw F D ε R QN QP).toMeasure=
      ((QN : Measure (PointMeasure ℝ≥0)).prod QP).map (compactClusterSuperposition F D ε R) := rfl

theorem lawConverges_compactWaistClusterPointMeasure_of_poisson
    (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,w,0}) (D : DeformationClassics F)
    {Ω : ℕ → Type w} [∀j,MeasurableSpace (Ω j)]
    (μ : (j : ℕ) → Measure (Ω j)) (X : (j : ℕ) → Ω j → PointMeasure ℝ≥0)
    (ν : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [NullSingletonClass ν]
    (QP : ProbabilityMeasure (PointMeasure ℝ≥0)) (hP : IsPoissonPointProcessLaw ℝ≥0 ν QP)
    (hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hX : ∀ᶠj in atTop,AEMeasurable (X j) (μ j))
    (hLaw : LawConverges μ X QP id) (ε R : ℝ≥0) (hε : 0<ε) :
    LawConverges μ (fun j ω => compactWaistClusterPointMeasure F D (X j ω) (waistWindow ε R))
      QP (fun ξ => compactWaistClusterPointMeasure F D ξ (waistWindow ε R)) := by
  exact lawConverges_compactWaistClusterPointMeasure F B C D μ X (QP : Measure (PointMeasure ℝ≥0)) id
    hprob hX aemeasurable_id hLaw ε R hε
    ((poisson_pointMeasure_no_atom_at ν QP hP ε (measure_singleton ε)).and
      (poisson_pointMeasure_no_atom_at ν QP hP R (measure_singleton R)))

theorem lawConverges_compactClusterSuperposition_of_poisson_parent
    (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,w,0}) (D : DeformationClassics F)
    {Ω : ℕ → Type w} [∀j,MeasurableSpace (Ω j)]
    (μ : (j : ℕ) → Measure (Ω j))
    (X : (j : ℕ) → Ω j → PointMeasure ℝ≥0 × PointMeasure ℝ≥0)
    (ν : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [NullSingletonClass ν]
    (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0)) (hP : IsPoissonPointProcessLaw ℝ≥0 ν QP)
    (hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hX : ∀ᶠj in atTop,AEMeasurable (X j) (μ j))
    (hLaw : LawConverges μ X ((QN : Measure (PointMeasure ℝ≥0)).prod QP) id)
    (ε R : ℝ≥0) (hε : 0<ε) :
    LawConverges μ (fun j ω => compactClusterSuperposition F D ε R (X j ω))
      (compactClusterSuperpositionLaw F D ε R QN QP) id := by
  have hzero := (poisson_pointMeasure_no_atom_at ν QP hP ε (measure_singleton ε)).and
    (poisson_pointMeasure_no_atom_at ν QP hP R (measure_singleton R))
  have hprod := (measurePreserving_snd
    (μ := (QN : Measure (PointMeasure ℝ≥0))) (ν := (QP : Measure (PointMeasure ℝ≥0)))).quasiMeasurePreserving.ae hzero
  have ht := lawConverges_compactClusterSuperposition F B C D μ X
    ((QN : Measure (PointMeasure ℝ≥0)).prod (QP : Measure (PointMeasure ℝ≥0))) id hprob hX aemeasurable_id hLaw ε R hε hprod
  intro f
  have he : (∫ξ,f ξ ∂compactClusterSuperpositionLaw F D ε R QN QP)=
      ∫p,f (compactClusterSuperposition F D ε R p) ∂(QN : Measure (PointMeasure ℝ≥0)).prod QP := by
    rw [compactClusterSuperpositionLaw_toMeasure]
    exact integral_map (compactClusterSuperposition_measurable F D ε R).aemeasurable
      f.continuous.aestronglyMeasurable
  simpa only [id_eq,he] using ht f

end WP.Critical.PantsCluster
