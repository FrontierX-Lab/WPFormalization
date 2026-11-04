import WPFormalization.Critical.ShortConfigurationRecordingNonsimpleMajorant
import WPFormalization.Critical.ShortConfigurationIntersectingMajorant

/-! Internal assembly for the fixed whole G.3 statement. The remaining
intersecting recording domination is an explicit paper obligation here;
this helper is not a classical interface or a completed Blueprint result. -/
noncomputable section
universe u v w z
namespace WP.Critical
open WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortActualCutRealizationGeometry
open WP.Critical.ShortConfiguration MeasureTheory Filter
open scoped ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u, v} P}
  {H : HyperbolicCurveGeometry.{u, v, w} G}

lemma intersecting_uniform_measurable_half_majorant_of_cut_domination
    (T : MulticurveTopology.{u, v, w, z} G H)
    (MI : MirzakhaniIntegration G H T) (r : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (c : ℝ) (hc : 0 < c)
    (hdom : ∀ n : ℕ → ℕ, ∀ᶠ g : ℕ in atTop,
      ∀ X : G.Moduli g (n g) (fun _ => 0),
        allShortIntersectingSimpleTupleCount T X r L ≤ intersectingCutMajorant T X r L) :
    UniformSequenceMeasurableHalfPowerMajorant
      (fun _ _ X => allShortIntersectingSimpleTupleCount T X r L) c := by
  obtain ⟨C, hC, hRate⟩ :=
    critical_intersectingCutMajorant_half_uniform_sequences T MI r L hL c hc
  refine ⟨C, hC, fun n hn => ⟨fun _ X => intersectingCutMajorant T X r L, ?_⟩⟩
  filter_upwards [hRate n hn, hdom n] with g hr hd
  exact ⟨(intersectingCutMajorant_measurable T MI r L).aemeasurable, hd, hr⟩

lemma complexShortConfigurationsConclusion_of_intersecting_cut_domination
    (A : AmbientRealization H) (T : MulticurveTopology.{u, v, w, z} G H)
    (AC : AmbientCurveCompatibility A T) (S : SingleCurvePieceClassics A)
    (Cuts : ActualCutRealizationData A T AC.complete_domain)
    (SC : SingleCurveCutCompanionData Cuts S)
    (MI : MirzakhaniIntegration G H T) (c : ℝ) (hc : 0 < c)
    (hdom : ∀ (r : ℕ) (L : ℝ), 0 ≤ L → ∀ n : ℕ → ℕ,
      ∀ᶠ g : ℕ in atTop, ∀ X : G.Moduli g (n g) (fun _ => 0),
        allShortIntersectingSimpleTupleCount T X r L ≤ intersectingCutMajorant T X r L) :
    ComplexShortConfigurationsConclusion A T S c := by
  apply complexShortConfigurationsConclusion_of_majorants A T S MI c hc
  · intro r L hL
    exact intersecting_uniform_measurable_half_majorant_of_cut_domination
      T MI r L hL c hc (hdom r L hL)
  · intro L hL
    exact nonsimpleNonPants_uniform_measurable_half_majorant A T AC S Cuts SC MI L hL c hc

end WP.Critical
