import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Quantitative outer-measure bounds need a measurable majorant. The event
itself need not be measurable, and no probability-space assumption is needed. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Filter
open scoped ENNReal Topology

lemma outer_probability_rate_of_majorant
    {Ω : ℕ → Type*} [∀ g, MeasurableSpace (Ω g)]
    (μ : (g : ℕ) → Measure (Ω g)) (A : (g : ℕ) → Set (Ω g))
    (M : (g : ℕ) → Ω g → ℝ≥0∞) (ρ : ℕ → ℝ)
    (hM : ∀ᶠ g in atTop, AEMeasurable (M g) (μ g))
    (hdom : ∀ᶠ g in atTop, ∀ X ∈ A g, 1 ≤ M g X)
    (hmean : ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      (∫⁻ X, M g X ∂μ g) ≤ ENNReal.ofReal (C * ρ g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      μ g (A g) ≤ ENNReal.ofReal (C * ρ g) := by
  obtain ⟨C, hC, hb⟩ := hmean
  refine ⟨C, hC, ?_⟩
  filter_upwards [hM, hdom, hb] with g hm hd hb
  exact (meas_le_lintegral₀ hm hd).trans hb

lemma outer_probability_real_rate
    {Ω : ℕ → Type*} [∀ g, MeasurableSpace (Ω g)]
    (μ : (g : ℕ) → Measure (Ω g)) (A : (g : ℕ) → Set (Ω g))
    (ρ : ℕ → ℝ) (hρ : ∀ g, 0 ≤ ρ g)
    (hb : ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      μ g (A g) ≤ ENNReal.ofReal (C * ρ g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      (μ g).real (A g) ≤ C * ρ g := by
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, hb.mono (fun g hg => ?_)⟩
  exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hg)
    ENNReal.ofReal_ne_top).mpr hg |>.trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hC.le (hρ g)))

lemma outer_probability_union_rate
    {Ω : ℕ → Type*} [∀ g, MeasurableSpace (Ω g)]
    (μ : (g : ℕ) → Measure (Ω g)) (A B : (g : ℕ) → Set (Ω g))
    (ρ : ℕ → ℝ) (hρ : ∀ g, 0 ≤ ρ g)
    (hA : ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      μ g (A g) ≤ ENNReal.ofReal (C * ρ g))
    (hB : ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      μ g (B g) ≤ ENNReal.ofReal (C * ρ g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      μ g (A g ∪ B g) ≤ ENNReal.ofReal (C * ρ g) := by
  obtain ⟨CA, hCA, hbA⟩ := hA
  obtain ⟨CB, hCB, hbB⟩ := hB
  refine ⟨CA + CB, add_pos hCA hCB, ?_⟩
  filter_upwards [hbA, hbB] with g ha hb
  calc
    _ ≤ μ g (A g) + μ g (B g) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (CA * ρ g) + ENNReal.ofReal (CB * ρ g) := add_le_add ha hb
    _ = ENNReal.ofReal ((CA + CB) * ρ g) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hCA.le (hρ g))
        (mul_nonneg hCB.le (hρ g)), add_mul]

end WP.Probability
