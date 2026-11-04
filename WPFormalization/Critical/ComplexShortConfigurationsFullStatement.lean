import WPFormalization.Critical.NonFillingPantsCounts
import WPFormalization.Critical.ComplexShortConfigurationsStatement

/-! The original whole G.3 statement, including literal complement filling.
This statement is independent of the choice S used to implement the stronger
support-count estimate. Both genuine measurable-majorant certificates are
retained as conclusions, with constants selected before all cusp sequences. -/
noncomputable section
universe u v w z
namespace WP.Critical
open WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortFullFillingGeometry MeasureTheory Filter
open scoped ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  (A : AmbientRealization H) (T : MulticurveTopology.{u,v,w,z} G H)

def FullComplexShortConfigurationsConclusion (c : ℝ) : Prop :=
  (∀ (r : ℕ) (L : ℝ), 0 ≤ L → UniformSequenceHalfPowerEstimate
    (fun _ _ X => allShortIntersectingSimpleTupleCount T X r L) c) ∧
  (∀ L : ℝ, 0 ≤ L → UniformSequenceHalfPowerEstimate
    (fun _ _ X => nonFillingPantsCount A X L) c) ∧
  (∀ n : ℕ → ℕ,
    Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c) →
    ∀ L : ℝ, 0 ≤ L →
      Tendsto (fun g => ∫⁻ X, separatingNonPantsCount T X L
        ∂wpProbability G g (n g)) atTop (𝓝 0)) ∧
  (∀ (r : ℕ) (L : ℝ), 0 ≤ L → UniformSequenceMeasurableHalfPowerMajorant
    (fun _ _ X => allShortIntersectingSimpleTupleCount T X r L) c) ∧
  (∀ L : ℝ, 0 ≤ L → UniformSequenceMeasurableHalfPowerMajorant
    (fun _ _ X => nonFillingPantsCount A X L) c)

lemma nonFillingPants_uniform_majorant_of_support_majorant
    (AC : AmbientCurveCompatibility A T) (S : SingleCurvePieceClassics A)
    (HF : FullSingleCurveFillingClassics A AC.complete_domain S)
    (L c : ℝ)
    (h : UniformSequenceMeasurableHalfPowerMajorant
      (fun _ _ X => nonsimpleNonPantsCount A S X L) c) :
    UniformSequenceMeasurableHalfPowerMajorant
      (fun _ _ X => nonFillingPantsCount A X L) c := by
  obtain ⟨C, hC, hM⟩ := h
  refine ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨M, hb⟩ := hM n hn
  refine ⟨M, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (2 : ℕ)] with g hg hg2
  refine ⟨hg.1, ?_, hg.2.2⟩
  intro X
  exact (nonFillingPantsCount_le_nonsimpleNonPantsCount A T AC S HF
    (show Stable g (n g) by unfold Stable; omega) X L).trans (hg.2.1 X)

lemma fullComplexShortConfigurationsConclusion_of_support_conclusion
    (AC : AmbientCurveCompatibility A T) (S : SingleCurvePieceClassics A)
    (HF : FullSingleCurveFillingClassics A AC.complete_domain S)
    (c : ℝ) (h : ComplexShortConfigurationsConclusion A T S c) :
    FullComplexShortConfigurationsConclusion A T c := by
  obtain ⟨hs, _, hsep, hsm, hnm⟩ := h
  have hfull : ∀ L : ℝ, 0 ≤ L → UniformSequenceMeasurableHalfPowerMajorant
      (fun _ _ X => nonFillingPantsCount A X L) c := by
    intro L hL
    exact nonFillingPants_uniform_majorant_of_support_majorant A T AC S HF L c (hnm L hL)
  exact ⟨hs, fun L hL => (hfull L hL).estimate, hsep, hsm, hfull⟩

end WP.Critical
