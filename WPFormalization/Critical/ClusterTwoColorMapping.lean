import WPFormalization.Critical.ClusterFiniteWaistMapping
import WPFormalization.Probability.PoissonNullWindows
import WPFormalization.Probability.TwoColorPointMeasuresLaws
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter WP.Probability TopologicalSpace Topology
open scoped ENNReal NNReal Topology CompactlySupported
variable (F : Family.{u,v})

lemma twoColor_poisson_right_no_atom_at
    (νN νP : Measure ℝ≥0) [IsLocallyFiniteMeasure νN] [IsLocallyFiniteMeasure νP]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure νN νP) Q)
    (s : ℝ≥0) (hs : νP {s}=0) :
    ∀ᵐξ ∂(Q : Measure (PointMeasure TwoColorSpace)),(twoColorDecode ξ).2.toMeasure {s}=0 := by
  let W : RelCompactBorelWindow ℝ≥0 :=
    ⟨{s},measurableSet_singleton s,by rw [isClosed_singleton.closure_eq];exact isCompact_singleton⟩
  have hν : twoColorMeasure νN νP (twoColorRightWindow W).carrier=0 := by
    exact (twoColorMeasure_inr νN νP W.carrier W.measurableSet).trans hs
  have ha := poisson_pointMeasure_null_window TwoColorSpace (twoColorMeasure νN νP) Q hQ
    (twoColorRightWindow W) hν
  filter_upwards [ha] with ξ hξ
  change ξ.toMeasure.comap Sum.inr {s}=0
  rw [IsOpenEmbedding.inr.measurableEmbedding.comap_apply]
  exact hξ

theorem lawConverges_compactClusterSuperposition_of_twoColor_poisson
    (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,w,0}) (D : DeformationClassics F)
    {Ω : ℕ → Type w} [∀j,MeasurableSpace (Ω j)]
    (μ : (j : ℕ) → Measure (Ω j))
    (X : (j : ℕ) → Ω j → PointMeasure ℝ≥0 × PointMeasure ℝ≥0)
    (νN νP : Measure ℝ≥0) [IsLocallyFiniteMeasure νN] [IsLocallyFiniteMeasure νP]
    [NullSingletonClass νP]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure νN νP) Q)
    (hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hX : ∀ᶠj in atTop,AEMeasurable (X j) (μ j))
    (hLaw : LawConverges μ X Q twoColorDecode) (ε R : ℝ≥0) (hε : 0<ε) :
    LawConverges μ (fun j ω => compactClusterSuperposition F D ε R (X j ω))
      Q (fun ξ => compactClusterSuperposition F D ε R (twoColorDecode ξ)) := by
  letI : MetrizableSpace (PointMeasure ℝ≥0) :=
    WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable.1
  letI : SecondCountableTopology (PointMeasure ℝ≥0) :=
    WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable.2
  exact lawConverges_compactClusterSuperposition F B C D μ X
    (Q : Measure (PointMeasure TwoColorSpace)) twoColorDecode hprob hX
    twoColorDecode_continuous.measurable.aemeasurable hLaw ε R hε
    ((twoColor_poisson_right_no_atom_at νN νP Q hQ ε (measure_singleton ε)).and
      (twoColor_poisson_right_no_atom_at νN νP Q hQ R (measure_singleton R)))

end WP.Critical.PantsCluster
