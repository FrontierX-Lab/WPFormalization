import WPFormalization.RandomGeometry.BoltzmannWpMixtureProcess
import WPFormalization.Tight.SpectrumPoissonConvergence
import WPFormalization.Probability.PointMeasureDilationConvergence
/-! The arbitrary subcritical Boltzmann tight-spectrum limit, assembled from
actual conditional WP laws and proved random-scale concentration. -/
noncomputable section
universe u v w
namespace WP.BoltzmannWp
open External Set MeasureTheory Filter WP.Probability
open scoped ENNReal NNReal Topology
universe z
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {T:TightRegions G} {H:HyperbolicCurveGeometry.{u,v,w} G}

theorem boltzmann_randomScale_poisson_law
    (T:TightRegions G) (BZ:BuddZonneveldTransform G T)
    (Q:TightGeodesicGeometry G T H) (A:TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI:BuddLionsTightIntegration G T H Q A) (D:BuddLionsTightGeometry G T H Q A)
    (BM:∀g n,(hg:2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (xs:ℕ→ℝ) (QL:ProbabilityMeasure (PointMeasure ℝ≥0))
    (hPPP:IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QL) :
    LawConverges (fun g=>wpMixture G g (xs g))
      (fun g=>observable G g (Tight.actualScaledTightPointMeasure Q g)) QL (fun ξ=>ξ) := by
  refine lawConverges_wpMixture P G (Tight.actualScaledTightPointMeasure Q)
    (QL:Measure (PointMeasure ℝ≥0)) (fun ξ:PointMeasure ℝ≥0=>ξ) xs ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with g hg n
    exact Tight.aemeasurable_actualScaledTightPointMeasure Q g n hg (BM g n hg)
  · intro gs hgs ns
    exact Tight.tight_spectrum_poisson_law_of_genus_tendsto T BZ Q A MI D BM gs ns hgs QL hPPP

theorem boltzmann_tight_spectrum_poisson_law
    (T:TightRegions G) (BZ:BuddZonneveldTransform G T)
    (Q:TightGeodesicGeometry G T H) (A:TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI:BuddLionsTightIntegration G T H Q A) (D:BuddLionsTightGeometry G T H Q A)
    (BM:∀g n,(hg:2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (μs:ℕ→ℝ) (hμ:∀g,μs g∈Ico (0:ℝ) muCritical)
    (QL:ProbabilityMeasure (PointMeasure ℝ≥0))
    (hPPP:IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QL) :
    LawConverges (fun g=>wpMixture G g (parameter (μs g)))
      (fun g=>physicalPointMeasure Q g (μs g) (hμ g)) QL (fun ξ=>ξ) := by
  have hprob : ∀ᶠg in atTop,IsProbabilityMeasure (wpMixture G g (parameter (μs g))) := by
    obtain ⟨N,hN⟩:=wpMixture_probability_eventually P G
    filter_upwards [eventually_ge_atTop N] with g hg
    exact hN g hg _
  have hXi : ∀ᶠg in atTop,AEMeasurable
      (observable G g (Tight.actualScaledTightPointMeasure Q g))
      (wpMixture G g (parameter (μs g))) := by
    filter_upwards [eventually_ge_atTop 2] with g hg
    exact observable_aemeasurable G g _ _ (fun n=>
      Tight.aemeasurable_actualScaledTightPointMeasure Q g n hg (BM g n hg))
  have ha : ∀ᶠg in atTop,AEMeasurable
      (fun X:Surface G g=>scaleRatio g (μs g) (hμ g) X.fst)
      (wpMixture G g (parameter (μs g))) :=
    Eventually.of_forall (fun g=>(measurable_scaleRatio G g (μs g) (hμ g)).aemeasurable)
  have he:=lawConverges_pointMeasureDilation
    (fun g=>wpMixture G g (parameter (μs g)))
    (fun g=>observable G g (Tight.actualScaledTightPointMeasure Q g))
    (fun g X=>scaleRatio g (μs g) (hμ g) X.fst) QL (fun ξ=>ξ)
    hprob hXi ha aemeasurable_id
    (boltzmann_randomScale_poisson_law T BZ Q A MI D BM (fun g=>parameter (μs g)) QL hPPP)
    (scaleRatio_in_probability P G (fun g=>g) tendsto_id μs hμ)
  simpa only [observable,physicalPointMeasure_dilation] using he

theorem boltzmann_tight_spectrum_poisson_limit
    (T:TightRegions G) (BZ:BuddZonneveldTransform G T)
    (Q:TightGeodesicGeometry G T H) (A:TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI:BuddLionsTightIntegration G T H Q A) (D:BuddLionsTightGeometry G T H Q A)
    (BM:∀g n,(hg:2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (μs:ℕ→ℝ) (hμ:∀g,μs g∈Ico (0:ℝ) muCritical) :
    ∃QL:ProbabilityMeasure (PointMeasure ℝ≥0),
      IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QL ∧
      LawConverges (fun g=>wpMixture G g (parameter (μs g)))
        (fun g=>physicalPointMeasure Q g (μs g) (hμ g)) QL (fun ξ=>ξ) := by
  obtain ⟨QL,hPPP⟩:=WP.External.poisson_point_process_exists ℝ≥0 nonseparatingLengthIntensity
  exact ⟨QL,hPPP,boltzmann_tight_spectrum_poisson_law T BZ Q A MI D BM μs hμ QL hPPP⟩
end WP.BoltzmannWp
