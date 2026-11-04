import WPFormalization.Critical.NonsimpleNonPantsCounts
import WPFormalization.Critical.MixedIntersectingDomination
import WPFormalization.Critical.SeparatingNonPantsEstimate

/-! Fixed mathematical statement of the WHOLE original G.3, independent of
its geometric implementation. Constants are chosen before the sequence n(g);
the eventual threshold may depend on that sequence. The stronger measurable
majorant certificates are separate paper proof obligations, never classical
interfaces. The final conclusion RETAINS both certificates as outputs: raw
lower Lebesgue integrals alone are insufficient without count measurability.
The certificates give the stronger outer-expectation bounds without assuming
Borelness of a geometric predicate. This module supplies no producer or
Blueprint completion label. -/
noncomputable section
universe u v w z
namespace WP.Critical
open WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open MeasureTheory Filter
open scoped ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u, v} P}

def UniformSequenceHalfPowerEstimate
    (F : (g n : ℕ) → G.Moduli g n (fun _ => 0) → ℝ≥0∞) (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
    Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c) →
    ∀ᶠ g : ℕ in atTop,
      (∫⁻ X, F g (n g) X ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C * (g : ℝ)^(-1/2 : ℝ))

def UniformSequenceMeasurableHalfPowerMajorant
    (F : (g n : ℕ) → G.Moduli g n (fun _ => 0) → ℝ≥0∞) (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
    Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c) →
    ∃ M : (g : ℕ) → G.Moduli g (n g) (fun _ => 0) → ℝ≥0∞,
      ∀ᶠ g : ℕ in atTop,
        AEMeasurable (M g) (wpProbability G g (n g)) ∧
        (∀ X, F g (n g) X ≤ M g X) ∧
        (∫⁻ X, M g X ∂wpProbability G g (n g)) ≤
          ENNReal.ofReal (C * (g : ℝ)^(-1/2 : ℝ))

lemma UniformSequenceMeasurableHalfPowerMajorant.estimate
    {F : (g n : ℕ) → G.Moduli g n (fun _ => 0) → ℝ≥0∞} {c : ℝ}
    (h : UniformSequenceMeasurableHalfPowerMajorant F c) :
    UniformSequenceHalfPowerEstimate F c := by
  obtain ⟨C, hC, hM⟩ := h
  refine ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨M, hb⟩ := hM n hn
  filter_upwards [hb] with g hg
  exact (lintegral_mono hg.2.1).trans hg.2.2

variable {H : HyperbolicCurveGeometry.{u, v, w} G}
  (A : AmbientRealization H) (T : MulticurveTopology.{u, v, w, z} G H)
  (S : SingleCurvePieceClassics A)

def ComplexShortConfigurationsConclusion (c : ℝ) : Prop :=
  (∀ (r : ℕ) (L : ℝ), 0 ≤ L → UniformSequenceHalfPowerEstimate
    (fun _ _ X => allShortIntersectingSimpleTupleCount T X r L) c) ∧
  (∀ L : ℝ, 0 ≤ L → UniformSequenceHalfPowerEstimate
    (fun _ _ X => nonsimpleNonPantsCount A S X L) c) ∧
  (∀ (n : ℕ → ℕ),
    Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c) →
    ∀ L : ℝ, 0 ≤ L →
      Tendsto (fun g => ∫⁻ X, separatingNonPantsCount T X L
        ∂wpProbability G g (n g)) atTop (𝓝 0)) ∧
  (∀ (r : ℕ) (L : ℝ), 0 ≤ L → UniformSequenceMeasurableHalfPowerMajorant
    (fun _ _ X => allShortIntersectingSimpleTupleCount T X r L) c) ∧
  (∀ L : ℝ, 0 ≤ L → UniformSequenceMeasurableHalfPowerMajorant
    (fun _ _ X => nonsimpleNonPantsCount A S X L) c)

/- Internal logical assembly only. Both hsimple and hnonsimple are unfinished
paper-specific certificates until the actual recording producers supply them. -/
lemma complexShortConfigurationsConclusion_of_majorants
    (MI : MirzakhaniIntegration G H T) (c : ℝ) (hc : 0 < c)
    (hsimple : ∀ (r : ℕ) (L : ℝ), 0 ≤ L →
      UniformSequenceMeasurableHalfPowerMajorant
        (fun _ _ X => allShortIntersectingSimpleTupleCount T X r L) c)
    (hnonsimple : ∀ L : ℝ, 0 ≤ L → UniformSequenceMeasurableHalfPowerMajorant
      (fun _ _ X => nonsimpleNonPantsCount A S X L) c) :
    ComplexShortConfigurationsConclusion A T S c := by
  refine ⟨fun r L hL => (hsimple r L hL).estimate,
    fun L hL => (hnonsimple L hL).estimate, ?_, hsimple, hnonsimple⟩
  intro n hn L hL
  exact critical_separatingNonPantsCount_tendsto_zero T MI L hL n c hc hn

lemma intersecting_moments_tendsto_zero_of_complexShortConfigurations
    {c : ℝ} (h : ComplexShortConfigurationsConclusion A T S c)
    (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c))
    (r : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    Tendsto (fun g => ∫⁻ X, allShortIntersectingSimpleTupleCount T X r L
      ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := h.1 r L hL
  have hzero : Tendsto (fun g : ℕ => ENNReal.ofReal (C * (g : ℝ)^(-1/2 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_const_nhds.mul critical_half_power_tendsto_zero)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    (Eventually.of_forall (fun _ => bot_le)) (hb n hn)

end WP.Critical
