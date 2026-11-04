import WPFormalization.Analysis.HarmonicEstimates

/-! The complete harmonic probability law, with uniform exponential moments and
the critical variance, proved from the actual normalized kernel. -/
noncomputable section
namespace WP
/- Probability law and uniform moment assertions in §2.2, including the critical variance. -/
/- Blueprint label(s): eq:P12
Paper v3: 2.8 [PDF 17]
Status: CONDITIONALLY_PROVED (classical Bessel real-zero and Pringsheim inputs)
-/
@[blueprint "eq:P12"]
theorem harmonic_law :
    (∀ Y ∈ Set.Icc 0 y₀,
      (∀ m, 0 ≤ harmonicMass Y m) ∧ HasSum (harmonicMass Y) 1 ∧
      HasSum (fun m : ℕ => (m : ℝ) * harmonicMass Y m) (3/2)) ∧
    (∃ c C t : ℝ, 0 < c ∧ 0 < C ∧ 0 < t ∧ ∀ Y ∈ Set.Icc 0 y₀,
      c ≤ harmonicMass Y 0 ∧ c ≤ harmonicMass Y 1 ∧
      c ≤ harmonicVariance Y ∧ harmonicVariance Y ≤ C ∧
      Summable (fun m : ℕ => Real.exp (t*m) * harmonicMass Y m) ∧
      ∑' m : ℕ, Real.exp (t*m) * harmonicMass Y m ≤ C) ∧
    harmonicVariance y₀ = 15/4 := by
  refine ⟨?_,Analysis.harmonic_uniform_bounds,Analysis.harmonicVariance_critical⟩
  intro Y hY
  exact ⟨fun m => (Analysis.harmonicMass_pos Y hY m).le,
    Analysis.harmonicMass_hasSum Y hY,Analysis.harmonicMass_mean Y hY⟩

end WP
