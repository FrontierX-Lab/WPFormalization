import WPFormalization.Critical.ClusterCanonicalMeasures
import WPFormalization.Probability.TwoColorLaplace

/- Full canonical-cluster Laplace formula from the actual two-color parent
PPP. All kernel statements are local consequences of the canonical family.
This does not assert ambient WP full-spectrum convergence. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set WP.Probability
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortComplementaryRegionGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortBorderedSingleCurveGeometry
open scoped NNReal ENNReal Topology CompactlySupported
variable (F : Family.{u,v})

lemma twoColor_clusterSuperposition_laplace (D : DeformationClassics F)
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure ν μ) Q)
    (f : C_c(ℝ≥0, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    (∫ ξ, PoissonCluster.laplaceObservable (fun x => f x)
      (clusterSuperposition F D hproper (twoColorDecode ξ)) ∂Q) =
      Real.exp (-(∫ x, 1 - Real.exp (-f x) ∂ν) - (∫ s, laplaceCostNN F f s ∂μ)) := by
  simp_rw [clusterSuperposition_laplaceObservable F D hproper]
  exact twoColor_poisson_joint_laplace ν μ Q hQ (fun x => f x) (testPairingNN F f)
    f.continuous.measurable (testPairingNN_measurable F D f) hf
    (testPairingNN_nonneg F f hf)
    ⟨‖f.toBoundedContinuousFunction‖,fun x => f.toBoundedContinuousFunction.apply_le_norm x⟩
    (testPairingNN_bounded_above F f)
    ⟨tsupport f, f.hasCompactSupport, subset_tsupport f⟩
    (testPairingNN_compact_support_of_prefix_cutoff F hproper f)

def twoColorClusterLaw (D : DeformationClassics F)
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace)) : ProbabilityMeasure (PointMeasure ℝ≥0) :=
  ⟨(Q : Measure (PointMeasure TwoColorSpace)).map
    (fun ξ => clusterSuperposition F D hproper (twoColorDecode ξ)), inferInstance⟩

lemma twoColorClusterLaw_toMeasure (D : DeformationClassics F)
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace)) :
    (twoColorClusterLaw F D hproper Q).toMeasure =
      (Q : Measure (PointMeasure TwoColorSpace)).map
        (fun ξ => clusterSuperposition F D hproper (twoColorDecode ξ)) := rfl

lemma twoColorClusterLaw_laplace (D : DeformationClassics F)
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure ν μ) Q)
    (f : C_c(ℝ≥0, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    (∫ ξ, PoissonCluster.laplaceObservable (fun x => f x) ξ ∂twoColorClusterLaw F D hproper Q) =
      Real.exp (-(∫ x, 1 - Real.exp (-f x) ∂ν) - (∫ s, laplaceCostNN F f s ∂μ)) := by
  have hd : Measurable twoColorDecode :=
    twoColorLeftProjection_continuous.measurable.prodMk twoColorRightProjection_continuous.measurable
  have hm : Measurable (fun ξ => clusterSuperposition F D hproper (twoColorDecode ξ)) :=
    (clusterSuperposition_measurable F D hproper).comp hd
  rw [twoColorClusterLaw_toMeasure, integral_map hm.aemeasurable]
  · exact twoColor_clusterSuperposition_laplace F D hproper ν μ Q hQ f hf
  · exact (Real.continuous_exp.comp (pointMeasure_vague_test_continuous f).neg).aestronglyMeasurable

lemma twoColor_canonicalClusterModel_laplace
    (D : DeformationClassics F)
    (BC : ∀ s, PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : ∀ s, BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀ s, BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀ s, BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure ν μ) Q)
    (f : C_c(ℝ≥0, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    (∫ ξ, PoissonCluster.laplaceObservable (fun x => f x)
      (clusterSuperposition F D (canonical_prefix_cutoff F BC LS J PC PP SC) (twoColorDecode ξ)) ∂Q) =
      Real.exp (-(∫ x, 1 - Real.exp (-f x) ∂ν) - (∫ s, laplaceCostNN F f s ∂μ)) :=
  twoColor_clusterSuperposition_laplace F D (canonical_prefix_cutoff F BC LS J PC PP SC) ν μ Q hQ f hf

end WP.Critical.PantsCluster
