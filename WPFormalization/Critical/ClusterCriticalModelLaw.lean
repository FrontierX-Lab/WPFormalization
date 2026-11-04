import WPFormalization.Critical.ClusterCriticalFullModel
import WPFormalization.Critical.ClusterTwoColorProductLaw
import WPFormalization.Probability.PointMeasureLaplaceTests

/- Internal canonical-model assembly, with actual WP parent observables.
This intermediate assembly retains an explicit G3 hypothesis. Its local
producer and the ambient full-spectrum identification are supplied downstream
in `CriticalPrimitiveLengthSpectrum.lean`, which carries the final Blueprint label. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd u v
namespace WP.Critical.PantsCluster
open WP.External WP.External.PantsCluster WP.RandomGeometry WP.Probability MeasureTheory Filter Set
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortComplementaryRegionGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortBorderedSingleCurveGeometry
open scoped NNReal ENNReal Topology CompactlySupported

lemma lawConverges_twoColorClusterLaw
    (F : Family.{u,v}) (D : DeformationClassics F)
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)
    {Ω : ℕ → Type*} [∀ j, MeasurableSpace (Ω j)]
    (μ : (j : ℕ) → Measure (Ω j)) (X : (j : ℕ) → Ω j → PointMeasure ℝ≥0)
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hLaw : LawConverges μ X Q (fun ξ => clusterSuperposition F D hproper (twoColorDecode ξ))) :
    LawConverges μ X (twoColorClusterLaw F D hproper Q) id := by
  intro f
  have ht := hLaw f
  have hd : Measurable twoColorDecode :=
    twoColorLeftProjection_continuous.measurable.prodMk twoColorRightProjection_continuous.measurable
  have hm : Measurable (fun ξ => clusterSuperposition F D hproper (twoColorDecode ξ)) :=
    (clusterSuperposition_measurable F D hproper).comp hd
  simpa only [twoColorClusterLaw_toMeasure, integral_map hm.aemeasurable
    f.continuous.aestronglyMeasurable, id_eq] using ht

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)

include MI RG in
lemma critical_canonicalClusterModelLaw_of_short_intersections
    (F : Family.{u,v}) (D : DeformationClassics F)
    (BC : ∀ s, PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : ∀ s, BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀ s, BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀ s, BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,bb,0})
    (I : WP.External.TwoColorPoissonRestrictionIndependence)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c))
    (hshort : ∀ t : ℕ, 2 ≤ t → ∀ L : ℝ, 0 ≤ L → Tendsto
      (fun g => ∫⁻ X, allShortIntersectingSimpleTupleCount T X t L
        ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    ∃ QN QP : ProbabilityMeasure (PointMeasure ℝ≥0),
      IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QN ∧
      IsPoissonPointProcessLaw ℝ≥0 (criticalPantsLengthIntensity c) QP ∧
      LawConverges (fun g => wpProbability G g (n g))
        (fun g X => clusterSuperposition F D (canonical_prefix_cutoff F BC LS J PC PP SC)
          (nonseparatingLengthPointMeasure T X, planarLengthPointMeasure H X 1 (by norm_num) 2))
        (canonicalClusterSuperpositionLaw F D BC LS J PC PP SC QN QP) id ∧
      ∀ (f : C_c(ℝ≥0, ℝ)), (∀ x, 0 ≤ f x) →
        Tendsto (fun g => ∫ X, PoissonCluster.laplaceObservable (fun x => f x)
          (clusterSuperposition F D (canonical_prefix_cutoff F BC LS J PC PP SC)
            (nonseparatingLengthPointMeasure T X, planarLengthPointMeasure H X 1 (by norm_num) 2))
          ∂wpProbability G g (n g)) atTop
          (𝓝 (Real.exp (-(∫ x, 1 - Real.exp (-f x) ∂nonseparatingLengthIntensity) -
            (∫ s, laplaceCostNN F f s ∂criticalPantsLengthIntensity c)))) := by
  obtain ⟨Q,hQ,hLaw⟩ := critical_canonicalClusterModel_of_short_intersections
    T MI RG F D BC LS J PC PP SC B C n c hc hn hshort
  have hprod := twoColorClusterLaw_eq_independent_product F D
    (canonical_prefix_cutoff F BC LS J PC PP SC) I
    nonseparatingLengthIntensity (criticalPantsLengthIntensity c) Q hQ
  have hweak := lawConverges_twoColorClusterLaw F D
    (canonical_prefix_cutoff F BC LS J PC PP SC) _ _ Q hLaw
  rw [hprod] at hweak
  refine ⟨twoColorLeftLaw Q,twoColorRightLaw Q,
    twoColorLeftLaw_poisson _ _ Q hQ,twoColorRightLaw_poisson _ _ Q hQ,hweak,?_⟩
  intro f hf
  have ht := PoissonCluster.lawConverges_laplaceObservable _ _ _ _ hLaw f hf
  rw [twoColor_canonicalClusterModel_laplace F D BC LS J PC PP SC
    nonseparatingLengthIntensity (criticalPantsLengthIntensity c) Q hQ f hf] at ht
  exact ht

end WP.Critical.PantsCluster
