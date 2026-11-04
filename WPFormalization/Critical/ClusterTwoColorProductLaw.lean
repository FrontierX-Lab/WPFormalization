import WPFormalization.Critical.ClusterTwoColorLaplace
import WPFormalization.Probability.TwoColorPoissonProduct
noncomputable section
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory WP.Probability Set
open scoped NNReal
universe u v

lemma twoColorClusterLaw_eq_independent_product
    (F : Family.{u,v}) (D : DeformationClassics F)
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)
    (C : WP.External.TwoColorPoissonRestrictionIndependence)
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure ν μ) Q) :
    twoColorClusterLaw F D hproper Q =
      clusterSuperpositionLaw F D hproper (twoColorLeftLaw Q) (twoColorRightLaw Q) := by
  apply Subtype.ext
  have hd : Measurable twoColorDecode :=
    twoColorLeftProjection_continuous.measurable.prodMk twoColorRightProjection_continuous.measurable
  change (Q : Measure (PointMeasure TwoColorSpace)).map
    (fun ξ => clusterSuperposition F D hproper (twoColorDecode ξ)) =
    ((twoColorLeftLaw Q : Measure (PointMeasure ℝ≥0)).prod (twoColorRightLaw Q)).map
      (clusterSuperposition F D hproper)
  rw [←twoColorDecode_map_eq_product C ν μ Q hQ,
    Measure.map_map (clusterSuperposition_measurable F D hproper) hd]
  rfl

end WP.Critical.PantsCluster
