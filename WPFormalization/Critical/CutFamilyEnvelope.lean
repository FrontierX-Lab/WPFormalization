import WPFormalization.Critical.CutFiniteCatalogRate
/-! Finite nonnegative integral sums preserve a common real envelope. -/
noncomputable section
namespace WP.Critical
open MeasureTheory Filter Finset
open scoped ENNReal Topology

lemma finite_lintegral_uniform_ofReal_envelope {ι : Type*} (s : Finset ι)
    {Ω : ℕ → Type*} [∀ g, MeasurableSpace (Ω g)] (μ : ∀ g, Measure (Ω g))
    (ρ : ℕ → ℝ) (hρ : ∀ g, 0 ≤ ρ g) (F : ι → ∀ g, Ω g → ℝ≥0∞)
    (hMeas : ∀ i ∈ s, ∀ g, Measurable (F i g))
    (hF : ∀ i ∈ s, ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      (∫⁻ x, F i g x ∂μ g) ≤ ENNReal.ofReal (C * ρ g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      (∫⁻ x, ∑ i ∈ s, F i g x ∂μ g) ≤ ENNReal.ofReal (C * ρ g) := by
  obtain ⟨C, hC, hb⟩ := finite_sum_uniform_ofReal_envelope s ρ hρ
    (fun i g => ∫⁻ x, F i g x ∂μ g) hF
  refine ⟨C, hC, hb.mono (fun g hg => ?_)⟩
  rwa [lintegral_finsetSum s (fun i hi => hMeas i hi g)]

lemma critical_half_envelope_tendsto_zero (F : ℕ → ℝ≥0∞)
    (hF : ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      F g ≤ ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ))) :
    Tendsto F atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := hF
  have ht : Tendsto (fun g : ℕ => ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_const_nhds.mul critical_half_power_tendsto_zero)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall (fun _ => bot_le)) hb
end WP.Critical
