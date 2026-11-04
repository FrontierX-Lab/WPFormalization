import WPFormalization.Critical.CutFamilyEnvelope
/-! Finite sums preserve constants chosen before an arbitrary parameter. -/
noncomputable section
namespace WP.Critical
open MeasureTheory Filter Finset
open scoped ENNReal Topology

lemma finite_sum_parameter_uniform_ofReal_envelope {ι σ : Type*} (s : Finset ι)
    (R : σ → Prop) (ρ : ℕ → ℝ) (hρ : ∀ g, 0 ≤ ρ g)
    (F : ι → σ → ℕ → ℝ≥0∞)
    (hF : ∀ i ∈ s, ∃ C : ℝ, 0 < C ∧ ∀ a, R a → ∀ᶠ g in atTop,
      F i a g ≤ ENNReal.ofReal (C * ρ g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a, R a → ∀ᶠ g in atTop,
      ∑ i ∈ s, F i a g ≤ ENNReal.ofReal (C * ρ g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, by norm_num, fun a ha => Eventually.of_forall (fun g => by simp)⟩
  | @insert i s hi ih =>
    obtain ⟨Ci, hCi, hbi⟩ := hF i (mem_insert_self _ _)
    obtain ⟨Cs, hCs, hbs⟩ := ih (fun j hj => hF j (mem_insert_of_mem hj))
    refine ⟨Ci + Cs, add_pos hCi hCs, ?_⟩
    intro a ha
    filter_upwards [hbi a ha, hbs a ha] with g hgi hgs
    rw [sum_insert hi]
    calc
      _ ≤ ENNReal.ofReal (Ci * ρ g) + ENNReal.ofReal (Cs * ρ g) := add_le_add hgi hgs
      _ = ENNReal.ofReal ((Ci + Cs) * ρ g) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hCi.le (hρ g))
          (mul_nonneg hCs.le (hρ g)), add_mul]

lemma finite_lintegral_parameter_uniform_ofReal_envelope {ι σ : Type*} (s : Finset ι)
    (R : σ → Prop) {Ω : σ → ℕ → Type*} [∀ a g, MeasurableSpace (Ω a g)]
    (μ : ∀ a g, Measure (Ω a g)) (ρ : ℕ → ℝ) (hρ : ∀ g, 0 ≤ ρ g)
    (F : ι → ∀ a g, Ω a g → ℝ≥0∞)
    (hMeas : ∀ i ∈ s, ∀ a g, Measurable (F i a g))
    (hF : ∀ i ∈ s, ∃ C : ℝ, 0 < C ∧ ∀ a, R a → ∀ᶠ g in atTop,
      (∫⁻ x, F i a g x ∂μ a g) ≤ ENNReal.ofReal (C * ρ g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a, R a → ∀ᶠ g in atTop,
      (∫⁻ x, ∑ i ∈ s, F i a g x ∂μ a g) ≤ ENNReal.ofReal (C * ρ g) := by
  obtain ⟨C, hC, hb⟩ := finite_sum_parameter_uniform_ofReal_envelope s R ρ hρ
    (fun i a g => ∫⁻ x, F i a g x ∂μ a g) hF
  refine ⟨C, hC, fun a ha => (hb a ha).mono (fun g hg => ?_)⟩
  rwa [lintegral_finsetSum s (fun i hi => hMeas i hi a g)]
end WP.Critical
