import WPFormalization.HigherOrder.Extraction

noncomputable section
namespace WP.HigherOrder

/- A single complex neighborhood works for every order. The complex functions
must restrict to the prescribed real coefficients, including both endpoints. -/
def GevreyExtensionPair (a L : ℕ → ℝ → ℝ) (C B : ℝ) : Prop :=
  ∃ (Ω : Set ℂ) (aC LC : ℕ → ℂ → ℂ), IsOpen Ω ∧
    (∀ Y ∈ Set.Icc 0 y₀, (Y : ℂ) ∈ Ω) ∧
    (∀ j, AnalyticOnNhd ℂ (aC j) Ω ∧ AnalyticOnNhd ℂ (LC j) Ω) ∧
    (∀ j Y, Y ∈ Set.Icc 0 y₀ → aC j Y = (a j Y : ℂ) ∧ LC j Y = (L j Y : ℂ)) ∧
    (∀ j z, z ∈ Ω → ‖aC j z‖ + ‖LC j z‖ ≤ C*B^j*(j.factorial : ℝ)^2)

/- The common-neighborhood requirement for the canonical extracted coefficients. -/
def GevreyExtension (A : ℕ → ℝ → ℝ) (C B : ℝ) : Prop :=
  ∃ (Ω : Set ℂ) (AC : ℕ → ℂ → ℂ), IsOpen Ω ∧
    (∀ Y ∈ Set.Icc 0 y₀, (Y : ℂ) ∈ Ω) ∧
    (∀ j, AnalyticOnNhd ℂ (AC j) Ω) ∧
    (∀ j Y, Y ∈ Set.Icc 0 y₀ → AC j Y = (A j Y : ℂ)) ∧
    (∀ j z, z ∈ Ω → ‖AC j z‖ ≤ C*B^j*(j.factorial : ℝ)^2)

end WP.HigherOrder
