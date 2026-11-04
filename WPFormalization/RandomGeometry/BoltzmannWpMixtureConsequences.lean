import WPFormalization.RandomGeometry.BoltzmannWpMixtureUnscaled
import WPFormalization.Probability.DilatedTightIntensity
noncomputable section
universe u v w z
namespace WP.BoltzmannWp
open External Set MeasureTheory Filter WP.Probability
open scoped ENNReal NNReal Topology
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {T:TightRegions G} {H:HyperbolicCurveGeometry.{u,v,w} G}

/-- The explicit-density, unscaled clause of Corollary 14.5, including
limiting weight zero. The intensity is (cosh(a_mu t)-1) dt/t. -/
theorem boltzmann_unscaled_tight_spectrum_limit
    (T:TightRegions G) (BZ:BuddZonneveldTransform G T)
    (Q:TightGeodesicGeometry G T H) (A:TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI:BuddLionsTightIntegration G T H Q A) (D:BuddLionsTightGeometry G T H Q A)
    (BM:∀g n,(hg:2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (μs:ℕ→ℝ) (hμs:∀g,μs g∈Ico (0:ℝ) muCritical)
    (μ:ℝ) (hμ:μ∈Ico (0:ℝ) muCritical) (ht:Tendsto μs atTop (𝓝 μ)) :
    letI := dilatedTightIntensity_locallyFinite (physicalScale μ) (physicalScale_pos μ hμ)
    ∃QL:ProbabilityMeasure (PointMeasure ℝ≥0),
      IsPoissonPointProcessLaw ℝ≥0 (dilatedTightIntensity (physicalScale μ)) QL ∧
      LawConverges (fun g=>wpMixture G g (parameter (μs g)))
        (fun g=>actualLengthPointMeasure Q g 1 (by norm_num)) QL (fun ξ=>ξ) := by
  obtain ⟨QL,hPPP⟩:=WP.External.poisson_point_process_exists ℝ≥0 nonseparatingLengthIntensity
  have ha:=physicalScale_pos μ hμ
  have hscale : (inversePhysicalScale μ hμ).val=Real.toNNReal ((physicalScale μ)⁻¹) := by
    apply NNReal.eq
    rw [inversePhysicalScale_coe,Real.coe_toNNReal _ (inv_pos.mpr ha).le]
  have hmap : nonseparatingLengthIntensity.map (fun x=>(inversePhysicalScale μ hμ).val*x)=
      dilatedTightIntensity (physicalScale μ) := by
    simpa only [hscale] using nonseparatingLengthIntensity_map_inverse (physicalScale μ) ha
  letI := dilatedTightIntensity_locallyFinite (physicalScale μ) ha
  letI : IsFiniteMeasureOnCompacts
      (nonseparatingLengthIntensity.map (fun x=>(inversePhysicalScale μ hμ).val*x)) := by
    rw [hmap]
    infer_instance
  refine ⟨QL.map (pointMeasureDilation (inversePhysicalScale μ hμ)),?_,?_⟩
  · have hp:=poissonLaw_pointMeasureDilation (inversePhysicalScale μ hμ)
      nonseparatingLengthIntensity QL hPPP
    simpa only [hmap] using hp
  · exact boltzmann_unscaled_tight_spectrum_law T BZ Q A MI D BM μs hμs μ hμ ht QL hPPP

/- Corollary 14.5 in full. The first assertion holds for every subcritical
weight sequence, in particular with arbitrary speed of approach to muCritical.
The second assertion identifies the unscaled limiting intensity at every fixed
subcritical limiting weight, including zero. -/
@[blueprint "cor:tight-boltzmann"]
theorem tight_boltzmann
    (T:TightRegions G) (BZ:BuddZonneveldTransform G T)
    (Q:TightGeodesicGeometry G T H) (A:TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI:BuddLionsTightIntegration G T H Q A) (D:BuddLionsTightGeometry G T H Q A)
    (BM:∀g n,(hg:2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (μs:ℕ→ℝ) (hμs:∀g,μs g∈Ico (0:ℝ) muCritical) :
    (∃QL:ProbabilityMeasure (PointMeasure ℝ≥0),
      IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QL ∧
      LawConverges (fun g=>wpMixture G g (parameter (μs g)))
        (fun g=>physicalPointMeasure Q g (μs g) (hμs g)) QL (fun ξ=>ξ)) ∧
    (∀μ:ℝ,∀hμ:μ∈Ico (0:ℝ) muCritical,Tendsto μs atTop (𝓝 μ)→
      letI := dilatedTightIntensity_locallyFinite (physicalScale μ) (physicalScale_pos μ hμ)
      ∃QL:ProbabilityMeasure (PointMeasure ℝ≥0),
        IsPoissonPointProcessLaw ℝ≥0 (dilatedTightIntensity (physicalScale μ)) QL ∧
        LawConverges (fun g=>wpMixture G g (parameter (μs g)))
          (fun g=>actualLengthPointMeasure Q g 1 (by norm_num)) QL (fun ξ=>ξ)) := by
  exact ⟨boltzmann_tight_spectrum_poisson_limit T BZ Q A MI D BM μs hμs,
    fun μ hμ ht=>boltzmann_unscaled_tight_spectrum_limit T BZ Q A MI D BM μs hμs μ hμ ht⟩
end WP.BoltzmannWp
