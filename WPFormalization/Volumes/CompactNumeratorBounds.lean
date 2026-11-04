import WPFormalization.Volumes.CompactRawMorseMatching
import WPFormalization.Analysis.UniformMorseFiniteModel
import WPFormalization.Analysis.CompactCoefficientPatching
/-! Original CG3 numerator coefficients have one Gevrey-two bound throughout the compact physical interval. The proof retains the actual S/l/Bc/f family, applies the common local Morse Cauchy bound, identifies the original coefficients at every point of each patch, then takes a finite subcover. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology
lemma compact_original_numerator_uniform_coefficient_bound
    (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hbc : b < xCritical)
    (S l Bc : ℂ → ℂ) (Ω : Set ℂ) (f : ℕ → ℂ → ℂ) (C B : ℝ)
    (hΩ : IsOpen Ω) (hcover : ∀ Y ∈ Icc (0 : ℝ) y₀, (Y : ℂ) ∈ Ω)
    (hC : 0 < C) (hB : 0 < B) (hf : ∀ j, AnalyticOnNhd ℂ (f j) Ω)
    (hfr : ∀ j Y, Y ∈ Icc (0 : ℝ) y₀ → f j (Y : ℂ) =
      (HigherOrder.markedCoefficient P p j Y : ℂ))
    (hbound : ∀ j z, z ∈ Ω → ‖f j z‖ ≤ C * B^j * (j.factorial : ℝ)^2)
    (hdata : ∀ x ∈ Icc a b, AnalyticAt ℂ S (x : ℂ) ∧ AnalyticAt ℂ l (x : ℂ) ∧
      ((fun t : ℝ => S (t : ℂ)) =ᶠ[𝓝 x] (fun t : ℝ => (extractionS t : ℂ))) ∧
      l (x : ℂ) = ((Real.sqrt (WP.euler WP.Psi x))⁻¹ : ℝ) ∧
      ∀ᶠ q : ℂ in 𝓝 (x : ℂ), (l q)^2 * ((complexEuler^[2]) S) q = 1)
    (hBc : ∀ x ∈ Ico (0 : ℝ) xCritical,
      AnalyticAt ℂ Bc (x : ℂ) ∧ Bc (x : ℂ) = (extractionB p x : ℂ)) :
    ∃ Cn Bn : ℝ, 0 < Cn ∧ 0 < Bn ∧ ∀ x ∈ Icc a b, ∀ j : ℕ,
      |PowerSeries.coeff j (extractionEvenNumerator P p x)| ≤ Cn * Bn^j * (j.factorial : ℝ)^2 := by
  apply compact_geometric_coefficient_patching (Icc a b) isCompact_Icc
    (fun x j => |PowerSeries.coeff j (extractionEvenNumerator P p x)|)
    (fun j => (j.factorial : ℝ)^2) (fun j => sq_nonneg _)
  intro x0 hx0
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Ioo (0 : ℝ) xCritical :=
    ⟨ha.trans_le hx.1, hx.2.trans_lt hbc⟩
  obtain ⟨d⟩ := exists_compact_morse_model_domain_at P p S l Bc x0 (hpoint x0 hx0)
    (hdata x0 hx0).1 (hdata x0 hx0).2.1 (hBc x0 ⟨(hpoint x0 hx0).1.le,(hpoint x0 hx0).2⟩).1
    (hBc x0 ⟨(hpoint x0 hx0).1.le,(hpoint x0 hx0).2⟩).2 (hdata x0 hx0).2.2.2.2
    Ω f C B hΩ hcover hC hB hf hbound
  let U : Set ℝ := {x | ‖(x : ℂ) - (x0 : ℂ)‖ < d.rho}
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hxU : x0 ∈ U := by simpa only [U,mem_ofPred_eq,sub_self,norm_zero] using d.rho_pos
  let Bn : ℝ := 2 * max B (2/d.R^2)
  have hBn : 0 < Bn := mul_pos (by norm_num) (hB.trans_le (le_max_left _ _))
  refine ⟨U,d.D,Bn,hU,hxU,d.D_pos,hBn,?_⟩
  intro x hx j
  let δ : ℂ := (x : ℂ) - (x0 : ℂ)
  have hδ : ‖δ‖ < d.rho := hx.2
  have hadd : (x0 : ℂ) + δ = (x : ℂ) := by dsimp [δ]; ring
  have hnum := compact_raw_numerator_coefficients_of_domain P p hp S l Bc (x0 : ℂ) Ω f B
    hΩ hcover hf hfr hBc d δ hδ x (hpoint x hx.1) hadd
    (hdata x hx.1).1 (hdata x hx.1).2.2.1 (hdata x hx.1).2.2.2.1
    (hdata x hx.1).2.2.2.2.self_of_nhds
  have he := gaussian_model_coefficients_gevrey_two
    (fun s u => morseTransformedAmplitude (compactMorseBase Bc l x0)
      (compactMorseParameter P l x0) f d.U s (δ,u)) d.D B d.R d.D_pos.le hB.le d.R_pos
    (d.post_diff δ hδ) (fun s u hu => d.bound δ hδ s u (Metric.sphere_subset_closedBall hu)) j
  rw [←hnum j] at he
  simpa only [extractionEvenNumerator,PowerSeries.coeff_mk,Complex.norm_real,Real.norm_eq_abs] using he
end WP.Analysis
