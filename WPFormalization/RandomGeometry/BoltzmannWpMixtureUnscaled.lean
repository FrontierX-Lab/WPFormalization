import WPFormalization.RandomGeometry.BoltzmannWpMixturePoisson
import WPFormalization.RandomGeometry.BoltzmannWpMixturePushforward
noncomputable section
universe u v w z
namespace WP.BoltzmannWp
open External Set MeasureTheory Filter WP.Probability
open scoped ENNReal NNReal Topology
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {T:TightRegions G} {H:HyperbolicCurveGeometry.{u,v,w} G}

def inversePhysicalScale (μ:ℝ) (hμ:μ∈Ico (0:ℝ) muCritical) : PositiveScale :=
  ⟨⟨(physicalScale μ)⁻¹,(inv_pos.mpr (physicalScale_pos μ hμ)).le⟩,
    by exact_mod_cast inv_pos.mpr (physicalScale_pos μ hμ)⟩

lemma inversePhysicalScale_coe (μ:ℝ) (hμ:μ∈Ico (0:ℝ) muCritical) :
    (((inversePhysicalScale μ hμ).val):ℝ)=(physicalScale μ)⁻¹ := rfl

lemma inversePhysicalScale_tendsto {μs:ℕ→ℝ} {μ:ℝ}
    (hμs:∀g,μs g∈Ico (0:ℝ) muCritical) (hμ:μ∈Ico (0:ℝ) muCritical)
    (ht:Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun g=>inversePhysicalScale (μs g) (hμs g)) atTop
      (𝓝 (inversePhysicalScale μ hμ)) := by
  apply tendsto_subtype_rng.mpr
  apply NNReal.tendsto_coe.mp
  exact (physicalScale_tendsto hμs hμ ht).inv₀ (physicalScale_pos μ hμ).ne'

lemma inversePhysicalScale_dilation (Q:TightGeodesicGeometry G T H)
    (g:ℕ) (μ:ℝ) (hμ:μ∈Ico (0:ℝ) muCritical) (X:Surface G g) :
    pointMeasureDilation (inversePhysicalScale μ hμ) (physicalPointMeasure Q g μ hμ X)=
      actualLengthPointMeasure Q g 1 (by norm_num) X := by
  have he:=curveLengthPointMeasure_dilation H
    (tightCuspSurface G ((tightCuspMeasurableEquiv G g X.fst).symm X.snd))
    (physicalScale μ) (physicalScale_pos μ hμ)
    (Q.cuspTight ((tightCuspMeasurableEquiv G g X.fst).symm X.snd))
    (inversePhysicalScale μ hμ)
  have hr : (((inversePhysicalScale μ hμ).val):ℝ)*physicalScale μ=1 := by
    rw [inversePhysicalScale_coe,inv_mul_cancel₀ (physicalScale_pos μ hμ).ne']
  simpa only [Tight.tightLengthPointMeasure,physicalPointMeasure,actualLengthPointMeasure,hr] using he

/-- Fixed subcritical limiting weight: the original unscaled full tight
catalogue converges, retaining the limiting positive inverse dilation. -/
theorem boltzmann_unscaled_tight_spectrum_law
    (T:TightRegions G) (BZ:BuddZonneveldTransform G T)
    (Q:TightGeodesicGeometry G T H) (A:TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI:BuddLionsTightIntegration G T H Q A) (D:BuddLionsTightGeometry G T H Q A)
    (BM:∀g n,(hg:2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (μs:ℕ→ℝ) (hμs:∀g,μs g∈Ico (0:ℝ) muCritical)
    (μ:ℝ) (hμ:μ∈Ico (0:ℝ) muCritical) (ht:Tendsto μs atTop (𝓝 μ))
    (QL:ProbabilityMeasure (PointMeasure ℝ≥0))
    (hPPP:IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QL) :
    LawConverges (fun g=>wpMixture G g (parameter (μs g)))
      (fun g=>actualLengthPointMeasure Q g 1 (by norm_num))
      (QL.map (pointMeasureDilation (inversePhysicalScale μ hμ))) (fun ξ=>ξ) := by
  let : TopologicalSpace.MetrizableSpace (PointMeasure NNReal) :=
    External.pointMeasure_nnreal_vague_metrizable_secondCountable.1
  let : SecondCountableTopology (PointMeasure NNReal) :=
    External.pointMeasure_nnreal_vague_metrizable_secondCountable.2
  letI : MetricSpace (PointMeasure NNReal) :=
    TopologicalSpace.metrizableSpaceMetric (PointMeasure NNReal)
  have hprob : ∀ᶠg in atTop,IsProbabilityMeasure (wpMixture G g (parameter (μs g))) := by
    obtain ⟨N,hN⟩:=wpMixture_probability_eventually P G
    filter_upwards [eventually_ge_atTop N] with g hg
    exact hN g hg _
  have hXi : ∀ᶠg in atTop,AEMeasurable (physicalPointMeasure Q g (μs g) (hμs g))
      (wpMixture G g (parameter (μs g))) := by
    filter_upwards [eventually_ge_atTop 2] with g hg
    exact aemeasurable_actualLengthPointMeasure Q g hg (fun n=>BM g n hg)
      _ _ _
  have htail : ∀δ>0,Tendsto (fun g=>(wpMixture G g (parameter (μs g))).real
      {X|δ≤dist (inversePhysicalScale (μs g) (hμs g)) (inversePhysicalScale μ hμ)}) atTop (𝓝 0) := by
    intro δ hδ
    apply tendsto_const_nhds.congr'
    filter_upwards [Metric.tendsto_nhds.mp (inversePhysicalScale_tendsto hμs hμ ht) δ hδ] with g hg
    have he : {X:Surface G g|δ≤dist (inversePhysicalScale (μs g) (hμs g))
        (inversePhysicalScale μ hμ)}=∅ := by
      ext X
      simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
      exact not_le.mpr hg
    simp [he]
  have hp:=lawConverges_prodMk_const_eventually
    (fun g=>wpMixture G g (parameter (μs g)))
    (fun g=>physicalPointMeasure Q g (μs g) (hμs g))
    (fun g (_:Surface G g)=>inversePhysicalScale (μs g) (hμs g))
    QL (fun ξ=>ξ) (inversePhysicalScale μ hμ) hprob hXi
    (Eventually.of_forall (fun _=>aemeasurable_const)) aemeasurable_id
    (boltzmann_tight_spectrum_poisson_law T BZ Q A MI D BM μs hμs QL hPPP) htail
  have he:=lawConverges_continuous_comp _ _ QL (fun ξ=>(ξ,inversePhysicalScale μ hμ))
    (fun p:PointMeasure NNReal×PositiveScale=>pointMeasureDilation p.2 p.1)
    (External.pointMeasure_nnreal_dilation_joint_continuous.comp continuous_swap) hp
  have he' : LawConverges (fun g=>wpMixture G g (parameter (μs g)))
      (fun g=>actualLengthPointMeasure Q g 1 (by norm_num)) QL
      (pointMeasureDilation (inversePhysicalScale μ hμ)) := by
    simpa only [inversePhysicalScale_dilation] using he
  intro f
  have hm : (∫ξ,f ξ ∂(QL.map (pointMeasureDilation (inversePhysicalScale μ hμ)):Measure _))=
      ∫ξ,f (pointMeasureDilation (inversePhysicalScale μ hμ) ξ) ∂QL :=
    integral_map (pointMeasureDilation_continuous_fixed _).measurable.aemeasurable
      f.continuous.aestronglyMeasurable
  rw [hm]
  exact he' f
end WP.BoltzmannWp
