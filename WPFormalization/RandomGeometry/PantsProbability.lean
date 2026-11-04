import Mathlib
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace WP.RandomGeometry

lemma normalized_square_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (a : ℝ) :
    (∫ ω, (X ω / a - 1)^2 ∂μ) =
      (∫ ω, X ω * (X ω - 1) ∂μ) / a^2 +
      (∫ ω, X ω ∂μ) / a^2 - 2 * (∫ ω, X ω ∂μ) / a + 1 := by
  have hi : Integrable X μ := hX.integrable (by norm_num)
  have hs := hX.integrable_sq
  have hf : Integrable (fun ω => X ω * (X ω - 1)) μ := by
    convert hs.sub hi using 1 <;> ext ω <;> simp only [Pi.sub_apply] <;> ring
  calc
    _ = ∫ ω, (X ω * (X ω - 1)) / a^2 + X ω / a^2 - 2 * X ω / a + 1 ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      ring
    _ = _ := by
      rw [integral_add (f := fun ω => (X ω * (X ω - 1)) / a^2 + X ω / a^2 - 2 * X ω / a) (g := fun _ => (1 : ℝ)) (((hf.div_const _).add (hi.div_const _)).sub ((hi.const_mul _).div_const _)) (integrable_const _),
        integral_sub (f := fun ω => (X ω * (X ω - 1)) / a^2 + X ω / a^2) (g := fun ω => 2 * X ω / a) ((hf.div_const _).add (hi.div_const _)) ((hi.const_mul _).div_const _),
        integral_add (f := fun ω => (X ω * (X ω - 1)) / a^2) (g := fun ω => X ω / a^2) (hf.div_const _) (hi.div_const _), integral_div, integral_div,
        integral_div, integral_const_mul]
      simp

lemma square_tail_real_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Integrable (fun ω => Y ω ^ 2) μ)
    (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |Y ω|} ≤ (∫ ω, Y ω^2 ∂μ) / ε^2 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => Y ω^2) (ae_of_all _ fun ω => sq_nonneg _) hY (ε^2)
  have he : {ω | ε^2 ≤ Y ω^2} = {ω | ε ≤ |Y ω|} := by
    ext ω
    change ε^2 ≤ Y ω^2 ↔ ε ≤ |Y ω|
    rw [← sq_abs (Y ω), sq_le_sq₀ hε.le (abs_nonneg _)]
  rw [he] at hm
  exact (le_div_iff₀ (sq_pos_of_pos hε)).2 (by simpa only [mul_comm] using hm)

lemma first_second_factorial_concentration
    {Ω : ℕ → Type*} [∀ g, MeasurableSpace (Ω g)]
    (μ : ∀ g, Measure (Ω g)) [∀ g, IsProbabilityMeasure (μ g)]
    (X : ∀ g, Ω g → ℝ) (hX : ∀ g, MemLp (X g) 2 (μ g))
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (hmean : Tendsto (fun g => (∫ ω, X g ω ∂μ g) / a g) atTop (𝓝 1))
    (hfactorial : Tendsto (fun g => (∫ ω, X g ω * (X g ω - 1) ∂μ g) / a g^2)
      atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun g => (μ g).real {ω | ε ≤ |X g ω / a g - 1|}) atTop (𝓝 0) := by
  have hinv : Tendsto (fun g => (a g)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp ha
  have hsecond : Tendsto (fun g => (∫ ω, X g ω ∂μ g) / a g^2) atTop (𝓝 0) := by
    have ht := hmean.mul hinv
    norm_num at ht
    convert ht using 1
    funext g
    simp [div_eq_mul_inv, pow_two]
    <;> ring
  have herr : Tendsto (fun g => ∫ ω, (X g ω / a g - 1)^2 ∂μ g) atTop (𝓝 0) := by
    simp_rw [normalized_square_integral (μ := μ _) (X := X _) (hX _)]
    convert ((hfactorial.add hsecond).sub (hmean.const_mul 2)).add_const 1 using 1 <;>
      norm_num [div_eq_mul_inv, mul_assoc]
  intro ε hε
  have hbound := herr.div_const (ε^2)
  simp only [zero_div] at hbound
  apply squeeze_zero (fun g => measureReal_nonneg) (fun g => ?_) hbound
  apply square_tail_real_le (μ g) _ _ ε hε
  have hi := ((hX g).const_mul (a g)⁻¹).sub (memLp_const (1 : ℝ))
  simpa only [Pi.sub_apply, div_eq_mul_inv, mul_comm] using hi.integrable_sq

lemma first_second_factorial_concentration_of_eventually
    {Ω : ℕ → Type*} [∀ g, MeasurableSpace (Ω g)]
    (μ : ∀ g, Measure (Ω g)) (hprob : ∀ᶠ g in atTop, IsProbabilityMeasure (μ g))
    (X : ∀ g, Ω g → ℝ) (hX : ∀ᶠ g in atTop, MemLp (X g) 2 (μ g))
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (hmean : Tendsto (fun g => (∫ ω, X g ω ∂μ g) / a g) atTop (𝓝 1))
    (hfactorial : Tendsto (fun g => (∫ ω, X g ω * (X g ω - 1) ∂μ g) / a g^2)
      atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun g => (μ g).real {ω | ε ≤ |X g ω / a g - 1|}) atTop (𝓝 0) := by
  have hinv : Tendsto (fun g => (a g)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp ha
  have hsecond : Tendsto (fun g => (∫ ω, X g ω ∂μ g) / a g^2) atTop (𝓝 0) := by
    have ht := hmean.mul hinv
    norm_num at ht
    convert ht using 1
    funext g
    simp [div_eq_mul_inv, pow_two]
    <;> ring
  have herr : Tendsto (fun g => ∫ ω, (X g ω / a g - 1)^2 ∂μ g) atTop (𝓝 0) := by
    have ht := ((hfactorial.add hsecond).sub (hmean.const_mul 2)).add_const 1
    norm_num at ht
    apply ht.congr'
    filter_upwards [hprob, hX] with g hg hXg
    letI : IsProbabilityMeasure (μ g) := hg
    simpa only [mul_div_assoc] using
      (normalized_square_integral (μ g) (X g) hXg (a g)).symm
  intro ε hε
  have hbound := herr.div_const (ε^2)
  simp only [zero_div] at hbound
  apply squeeze_zero' (Eventually.of_forall fun g => measureReal_nonneg) ?_ hbound
  filter_upwards [hprob, hX] with g hg hXg
  letI : IsProbabilityMeasure (μ g) := hg
  apply square_tail_real_le (μ g) _ _ ε hε
  have hi := (hXg.const_mul (a g)⁻¹).sub (memLp_const (1 : ℝ))
  simpa only [Pi.sub_apply, div_eq_mul_inv, mul_comm] using hi.integrable_sq
end WP.RandomGeometry
