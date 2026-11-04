import WPFormalization.Critical.ClusterCriticalFiniteModel
import WPFormalization.Critical.ClusterFullMapping
import WPFormalization.Critical.PantsClusterSupportProducer
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd u v w
namespace WP.Critical.PantsCluster
open WP.External WP.External.PantsCluster WP.RandomGeometry WP.Probability MeasureTheory Filter Set TopologicalSpace
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortComplementaryRegionGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortBorderedSingleCurveGeometry
open scoped Classical ENNReal NNReal Topology

lemma lawConverges_clusterSuperposition_of_twoColor_poisson
    (F : Family.{u,v}) (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,w,0}) (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    {Ω : ℕ → Type w} [∀j,MeasurableSpace (Ω j)]
    (μ : (j : ℕ) → Measure (Ω j))
    (X : (j : ℕ) → Ω j → PointMeasure ℝ≥0 × PointMeasure ℝ≥0)
    (νN νP : Measure ℝ≥0) [IsLocallyFiniteMeasure νN] [IsLocallyFiniteMeasure νP]
    [NullSingletonClass νP]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure νN νP) Q)
    (hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hX : ∀ᶠj in atTop,AEMeasurable (X j) (μ j))
    (hLaw : LawConverges μ X Q twoColorDecode) :
    LawConverges μ (fun j ω => clusterSuperposition F D hproper (X j ω))
      Q (fun ξ => clusterSuperposition F D hproper (twoColorDecode ξ)) := by
  letI : MetrizableSpace (PointMeasure ℝ≥0) :=
    WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable.1
  letI : SecondCountableTopology (PointMeasure ℝ≥0) :=
    WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable.2
  exact lawConverges_clusterSuperposition F B C D hproper μ X
    (Q : Measure (PointMeasure TwoColorSpace)) twoColorDecode hprob hX
    twoColorDecode_continuous.measurable.aemeasurable hLaw
    (twoColor_poisson_right_no_atom_at νN νP Q hQ 0 (measure_singleton 0))

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)

/- This is still an internal canonical-model result. The only remaining
paper-specific input here is G3 short-intersection vanishing. Relating the
ambient full primitive process to the canonical model is a separate proof. -/
include MI RG in
lemma critical_clusterSuperposition_of_short_intersections
    (F : Family.{u,v}) (D : DeformationClassics F)
    (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,bb,0})
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (hshort : ∀t : ℕ,2≤t→∀L : ℝ,0≤L→Tendsto
      (fun g => ∫⁻ X,allShortIntersectingSimpleTupleCount T X t L
        ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    ∃Q : ProbabilityMeasure (PointMeasure TwoColorSpace),
      IsPoissonPointProcessLaw TwoColorSpace (criticalTwoColorIntensity c) Q ∧
      LawConverges (fun g => wpProbability G g (n g))
        (fun g X => clusterSuperposition F D hproper
          (nonseparatingLengthPointMeasure T X,planarLengthPointMeasure H X 1 (by norm_num) 2))
        Q (fun ξ => clusterSuperposition F D hproper (twoColorDecode ξ)) := by
  obtain ⟨Q,hQ,hweak⟩ := critical_mixed_poisson_pair_of_short_intersections T MI RG n c hc hn hshort
  refine ⟨Q,hQ,?_⟩
  apply lawConverges_clusterSuperposition_of_twoColor_poisson F B C D hproper
    (fun g => wpProbability G g (n g))
    (fun g X => (nonseparatingLengthPointMeasure T X,planarLengthPointMeasure H X 1 (by norm_num) 2))
    nonseparatingLengthIntensity (criticalPantsLengthIntensity c) Q hQ
    (WP.Spectral.wpProbability_eventually_probability P G n
      ((surviving_critical_cusps_tendsto n c hc hn).eventually_ge_atTop 1))
    _ hweak
  filter_upwards [] with g
  exact critical_parent_pair_aemeasurable T MI g (n g)

include MI RG in
lemma critical_canonicalClusterModel_of_short_intersections
    (F : Family.{u,v}) (D : DeformationClassics F)
    (BC : ∀s,PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : ∀s,BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀s,BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀s,BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,bb,0})
    (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (hshort : ∀t : ℕ,2≤t→∀L : ℝ,0≤L→Tendsto
      (fun g => ∫⁻ X,allShortIntersectingSimpleTupleCount T X t L
        ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    ∃Q : ProbabilityMeasure (PointMeasure TwoColorSpace),
      IsPoissonPointProcessLaw TwoColorSpace (criticalTwoColorIntensity c) Q ∧
      LawConverges (fun g => wpProbability G g (n g))
        (fun g X => clusterSuperposition F D (canonical_prefix_cutoff F BC LS J PC PP SC)
          (nonseparatingLengthPointMeasure T X,planarLengthPointMeasure H X 1 (by norm_num) 2))
        Q (fun ξ => clusterSuperposition F D (canonical_prefix_cutoff F BC LS J PC PP SC) (twoColorDecode ξ)) :=
  critical_clusterSuperposition_of_short_intersections T MI RG F D B C
    (canonical_prefix_cutoff F BC LS J PC PP SC) n c hc hn hshort

end WP.Critical.PantsCluster
