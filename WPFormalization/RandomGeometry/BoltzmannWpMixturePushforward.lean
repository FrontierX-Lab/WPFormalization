import WPFormalization.Probability.PointMeasureDilationConvergence
import WPFormalization.External.PointProcessProbability
noncomputable section
namespace WP.BoltzmannWp
open External Set MeasureTheory Filter ProbabilityTheory WP.Probability
open scoped ENNReal NNReal Topology

def dilationPreimageWindow (a:PositiveScale) (B:RelCompactBorelWindow ℝ≥0) :
    RelCompactBorelWindow ℝ≥0 where
  carrier := (fun x=>a.val*x)⁻¹' B.carrier
  measurableSet := B.measurableSet.preimage (by fun_prop)
  compactClosure := by
    let e:=Homeomorph.mulLeft₀ a.val a.property.ne'
    change IsCompact (closure (e⁻¹' B.carrier))
    rw [←e.preimage_closure]
    exact e.isCompact_preimage.mpr B.compactClosure

lemma pointMeasureDilation_count (a:PositiveScale) (ξ:PointMeasure ℝ≥0)
    (B:RelCompactBorelWindow ℝ≥0) :
    (pointMeasureDilation a ξ).count ℝ≥0 B=ξ.count ℝ≥0 (dilationPreimageWindow a B) := by
  have hm : ((pointMeasureDilation a ξ).count ℝ≥0 B:ℝ≥0∞)=
      (ξ.count ℝ≥0 (dilationPreimageWindow a B):ℝ≥0∞) := by
    rw [←(pointMeasureDilation a ξ).count_spec,pointMeasureDilation_toMeasure,
      Measure.map_apply (by fun_prop) B.measurableSet]
    exact ξ.count_spec ℝ≥0 (dilationPreimageWindow a B)
  exact_mod_cast hm

lemma dilationPreimageWindow_disjoint {d:ℕ} (a:PositiveScale)
    (B:Fin d→RelCompactBorelWindow ℝ≥0) (hd:DisjointWindows ℝ≥0 B) :
    DisjointWindows ℝ≥0 (fun i=>dilationPreimageWindow a (B i)) := by
  intro i j hij
  exact (hd hij).preimage _

lemma dilation_windowRates {d:ℕ} (a:PositiveScale) (ν:Measure ℝ≥0)
    (B:Fin d→RelCompactBorelWindow ℝ≥0) :
    windowRates ℝ≥0 (ν.map (fun x=>a.val*x)) B=
      windowRates ℝ≥0 ν (fun i=>dilationPreimageWindow a (B i)) := by
  funext i
  unfold windowRates
  rw [Measure.map_apply (by fun_prop) (B i).measurableSet]
  rfl

/-- Deterministic positive dilation carries the actual PPP law to the PPP
whose intensity is the same ordinary pushforward measure. -/
theorem poissonLaw_pointMeasureDilation (a:PositiveScale)
    (ν:Measure ℝ≥0) [IsFiniteMeasureOnCompacts ν]
    [IsFiniteMeasureOnCompacts (ν.map (fun x=>a.val*x))]
    (QL:ProbabilityMeasure (PointMeasure ℝ≥0))
    (hPPP:IsPoissonPointProcessLaw ℝ≥0 ν QL) :
    IsPoissonPointProcessLaw ℝ≥0 (ν.map (fun x=>a.val*x))
      (QL.map (pointMeasureDilation a)) := by
  intro d B hd
  have hOrig:=hPPP d (fun i=>dilationPreimageWindow a (B i))
    (dilationPreimageWindow_disjoint a B hd)
  have hm : Measurable (windowCountVector ℝ≥0 B) := by
    apply measurable_pi_lambda
    intro i
    exact WP.External.pointMeasure_count_measurable ℝ≥0 (B i)
  refine ⟨hm.aemeasurable,?_⟩
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_map hm (pointMeasureDilation_continuous_fixed a).measurable,
    dilation_windowRates]
  have he : (windowCountVector ℝ≥0 B)∘pointMeasureDilation a=
      windowCountVector ℝ≥0 (fun i=>dilationPreimageWindow a (B i)) := by
    funext ξ i
    exact pointMeasureDilation_count a ξ (B i)
  rw [he]
  exact hOrig.map_eq
end WP.BoltzmannWp
