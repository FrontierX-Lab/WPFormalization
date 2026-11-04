import WPFormalization.Critical.ComplexShortConfigurationsStatement
import WPFormalization.Critical.MixedPoissonConsumer
import WPFormalization.Probability.TwoColorPoissonProduct
import WPFormalization.External.PointMeasureDilationTopology

/- Fixed full statement of original G.4: the actual unscaled nonseparating
and two-cusp-waist point measures converge jointly to independent PPPs.
The assembly below still takes the paper's G3 conclusion as an ordinary
internal premise; it has no final Blueprint label until that premise is
supplied by its actual local producer. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical
open WP.External WP.RandomGeometry WP.Probability MeasureTheory Filter Set
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  (T : MulticurveTopology.{u,v,w,z} G H)

def CriticalJointPoissonLimit (n : ℕ → ℕ) (c : ℝ) : Prop :=
  ∃ QN QP : ProbabilityMeasure (PointMeasure ℝ≥0),
    IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QN ∧
    IsPoissonPointProcessLaw ℝ≥0 (criticalPantsLengthIntensity c) QP ∧
    LawConverges (fun g => wpProbability G g (n g))
      (fun g X => (nonseparatingLengthPointMeasure T X,
        planarLengthPointMeasure H X 1 (by norm_num) 2))
      ((QN : Measure (PointMeasure ℝ≥0)).prod QP) id

lemma critical_jointPoissonLimit_of_short_intersections
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)
    (I : WP.External.TwoColorPoissonRestrictionIndependence)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c))
    (hshort : ∀ t : ℕ, 2 ≤ t → ∀ L : ℝ, 0 ≤ L → Tendsto
      (fun g => ∫⁻ X, allShortIntersectingSimpleTupleCount T X t L
        ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    CriticalJointPoissonLimit T n c := by
  obtain ⟨Q,hQ,hweak⟩ := critical_mixed_poisson_pair_of_short_intersections T MI RG n c hc hn hshort
  refine ⟨twoColorLeftLaw Q,twoColorRightLaw Q,
    twoColorLeftLaw_poisson _ _ Q hQ,twoColorRightLaw_poisson _ _ Q hQ,?_⟩
  letI : SecondCountableTopology (PointMeasure ℝ≥0) :=
    WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable.2
  have hd : Measurable twoColorDecode :=
    twoColorLeftProjection_continuous.measurable.prodMk twoColorRightProjection_continuous.measurable
  intro f
  have ht := hweak f
  have hprod := twoColorDecode_map_eq_product I nonseparatingLengthIntensity
    (criticalPantsLengthIntensity c) Q hQ
  have hi : (∫ ξ, f (twoColorDecode ξ) ∂Q) =
      ∫ ξ, f ξ ∂(twoColorLeftLaw Q : Measure (PointMeasure ℝ≥0)).prod (twoColorRightLaw Q) := by
    rw [←hprod,integral_map hd.aemeasurable f.continuous.aestronglyMeasurable]
  simpa only [hi,id_eq] using ht

lemma critical_jointPoissonLimit_of_complexShortConfigurations
    (A : AmbientRealization H) (S : SingleCurvePieceClassics A)
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)
    (I : WP.External.TwoColorPoissonRestrictionIndependence)
    (c : ℝ) (hc : 0 < c) (hG3 : ComplexShortConfigurationsConclusion A T S c)
    (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    CriticalJointPoissonLimit T n c := by
  apply critical_jointPoissonLimit_of_short_intersections T MI RG I n c hc hn
  intro t _ L hL
  exact intersecting_moments_tendsto_zero_of_complexShortConfigurations A T S hG3 n hn t L hL

end WP.Critical
