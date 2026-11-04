import WPFormalization.Probability.PointMeasureDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Weak-law transfer through events whose probabilities vanish.
The laws are genuine bounded-continuous-test laws, on varying source spaces. -/
noncomputable section
universe u v w
namespace WP.Probability
open MeasureTheory Filter Set
open scoped Topology

/-- A bounded continuous observable is integrable after an almost-everywhere
measurable random variable, for every finite source measure. -/
lemma boundedContinuousFunction_integrable_comp {E : Type u} [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → E) (hX : AEMeasurable X μ)
    (f : BoundedContinuousFunction E ℝ) : Integrable (fun ω => f (X ω)) μ := by
  apply Integrable.of_bound (f.continuous.measurable.comp_aemeasurable hX).aestronglyMeasurable ‖f‖
  exact Eventually.of_forall fun ω => f.norm_coe_le_norm (X ω)

/-- If two random variables agree outside a measurable bad event, their
bounded-continuous-test integrals differ by at most twice the test norm times
the measure of that event. No distribution-specific assumptions are used. -/
lemma boundedContinuousFunction_integral_sub_le_bad_event {E : Type u} [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y : Ω → E)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (A : Set Ω)
    (_hA : MeasurableSet A) (hXY : ∀ω,ω ∉ A → X ω=Y ω)
    (f : BoundedContinuousFunction E ℝ) :
    ‖(∫ ω,f (X ω) ∂μ)-(∫ ω,f (Y ω) ∂μ)‖ ≤ 2*‖f‖*μ.real A := by
  have hiX := boundedContinuousFunction_integrable_comp μ X hX f
  have hiY := boundedContinuousFunction_integrable_comp μ Y hY f
  have he : (∫ ω,f (X ω)-f (Y ω) ∂μ)=(∫ ω in A,f (X ω)-f (Y ω) ∂μ) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro ω hω
    rw [hXY ω hω,sub_self]
  rw [←integral_sub hiX hiY,he]
  apply norm_setIntegral_le_of_norm_le_const (measure_lt_top μ A)
  intro ω _
  calc
    ‖f (X ω)-f (Y ω)‖ ≤ ‖f (X ω)‖+‖f (Y ω)‖ := norm_sub_le _ _
    _ ≤ ‖f‖+‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
    _ = 2*‖f‖ := by ring

/-- Altering a random variable only on events whose probabilities vanish
preserves weak-law convergence. The probability and measurability conditions
need only hold eventually; source probability spaces may vary with the index. -/
theorem lawConverges_of_eq_off_bad_events {E : Type u} [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {Ω : ℕ → Type v}
    [∀j,MeasurableSpace (Ω j)] {Ωlimit : Type w} [MeasurableSpace Ωlimit]
    (μ : (j : ℕ) → Measure (Ω j)) (X Y : (j : ℕ) → Ω j → E)
    (Q : Measure Ωlimit) (Z : Ωlimit → E)
    (hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hX : ∀ᶠj in atTop,AEMeasurable (X j) (μ j))
    (hY : ∀ᶠj in atTop,AEMeasurable (Y j) (μ j))
    (A : (j : ℕ) → Set (Ω j)) (hA : ∀ᶠj in atTop,MeasurableSet (A j))
    (hXY : ∀ᶠj in atTop,∀ω,ω ∉ A j → X j ω=Y j ω)
    (hbad : Tendsto (fun j => (μ j).real (A j)) atTop (𝓝 0))
    (hLaw : LawConverges μ Y Q Z) : LawConverges μ X Q Z := by
  intro f
  have hbound : ∀ᶠj in atTop,
      ‖(∫ ω,f (X j ω) ∂μ j)-(∫ ω,f (Y j ω) ∂μ j)‖ ≤
        2*‖f‖*(μ j).real (A j) := by
    filter_upwards [hprob,hX,hY,hA,hXY] with j hp hx hy ha hxy
    haveI := hp
    exact boundedContinuousFunction_integral_sub_le_bad_event (μ j) (X j) (Y j) hx hy (A j) ha hxy f
  have ht := hbad.const_mul (2*‖f‖)
  simp only [mul_zero] at ht
  have hnorm := squeeze_zero' (Eventually.of_forall (fun j => norm_nonneg
    ((∫ ω,f (X j ω) ∂μ j)-(∫ ω,f (Y j ω) ∂μ j)))) hbound ht
  have hzero := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hs := hzero.add (hLaw f)
  simpa only [zero_add,sub_add_cancel] using hs

end WP.Probability
