import Mathlib.Probability.Martingale.OptionalStopping
import VersoBlueprint.Attribute

/-! Bounded optional stopping in the supermartingale direction.

This is Mathlib's `Submartingale.expected_stoppedValue_mono` applied to the
negative supermartingale, with the earlier stopping time equal to zero.
A deterministic finite-complexity bound is one possible stopping bound; no
particular random process is assumed here. The paper's current comparison
proof instead uses `WP.Analysis.finite_rank_log_lower` and does not depend on
this module. Nonnegativity is unnecessary for an integrable supermartingale.
-/
noncomputable section
universe u
namespace WP.Probability
open MeasureTheory

/- A real supermartingale on a probability space has expected value at a
bounded natural-time stopping time at most its initial expectation. -/
@[blueprint "ext:optional-stopping"]
theorem bounded_optional_stopping {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    {f : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    (hf : Supermartingale f ℱ μ) (hτ : IsStoppingTime ℱ τ)
    (N : ℕ) (hbounded : ∀ ω, τ ω ≤ N) :
    (∫ ω, stoppedValue f τ ω ∂μ) ≤ ∫ ω, f 0 ω ∂μ := by
  have h := hf.neg.expected_stoppedValue_mono
    (isStoppingTime_const ℱ (0 : ℕ)) hτ (fun _ => bot_le) hbounded
  simpa only [stoppedValue_const, stoppedValue_neg, Pi.neg_apply, integral_neg,
    neg_le_neg_iff] using h

end WP.Probability
