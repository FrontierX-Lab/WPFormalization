import WPFormalization.Volumes.CompactFixedModelData
/-! Given the previously selected actual physical S/l/Bc and canonical f/B, one common complex tube controls the SAME normalized phase and all pre-Morse amplitudes. No phase, amplitude, coefficient family or optimal cutoff is reselected. This supplies uniform analyticity and Gaussian growth for the subsequent actual central Fourier client. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma compact_uniform_model_data_of_given_physical_family (P : PsiTheory) (p : ℕ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b < xCritical)
    (S l Bc : ℂ → ℂ)
    (hS : ∀ x ∈ Icc a b, AnalyticAt ℂ S (x : ℂ))
    (hl : ∀ x ∈ Icc a b, AnalyticAt ℂ l (x : ℂ))
    (hunit : ∀ x ∈ Icc a b, ∀ᶠ q : ℂ in 𝓝 (x : ℂ), (l q)^2 * ((complexEuler^[2]) S) q = 1)
    (hBc : ∀ x ∈ Ico (0 : ℝ) xCritical, AnalyticAt ℂ Bc (x : ℂ) ∧ Bc (x : ℂ) = (extractionB p x : ℂ))
    (Ωf : Set ℂ) (f : ℕ → ℂ → ℂ) (C0 B : ℝ) (hΩf : IsOpen Ωf)
    (hcover : ∀ Y ∈ Icc (0 : ℝ) y₀, (Y : ℂ) ∈ Ωf) (hC0 : 0 < C0) (hB : 0 < B)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) Ωf)
    (hfr : ∀ j Y, Y ∈ Icc (0 : ℝ) y₀ → f j (Y : ℂ) = (HigherOrder.markedCoefficient P p j Y : ℂ))
    (hfb : ∀ j z, z ∈ Ωf → ‖f j z‖ ≤ C0 * B^j * (j.factorial : ℝ)^2) :
    ∃ (Ω : Set ℂ) (r C : ℝ), IsOpen Ω ∧ (∀ x ∈ Icc a b, (x : ℂ) ∈ Ω) ∧
      0 < r ∧ 0 < C ∧
      (∀ j, AnalyticOnNhd ℂ (compactPremorseAmplitude P Bc l f j) (Ω ×ˢ Metric.ball 0 r)) ∧
      ∀ x ∈ Ω, ∀ u : ℂ, ‖u‖ < r →
        AnalyticAt ℂ (centeredExponentialPhase S l) (x,u) ∧
        ‖centeredExponentialPhase S l (x,u)‖ ≤ ‖u‖^2 ∧
        ‖compactModelPoint l (x,u)‖ < xCritical ∧
        ∀ j, ‖compactPremorseAmplitude P Bc l f j (x,u)‖ ≤ C * B^j * (j.factorial : ℝ)^2 := by
  let K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hF : ∀ x ∈ K, AnalyticAt ℂ (centeredExponentialPhase S l) (x,0) := by
    rintro x ⟨t,ht,rfl⟩
    exact centeredExponentialPhase_analyticAt S l t (hS t ht) (hl t ht)
  have hj : ∀ x ∈ K, ∀ᶠ q : ℂ in 𝓝 x, centeredExponentialPhase S l (q,0) = 0 ∧
      deriv (fun u : ℂ => centeredExponentialPhase S l (q,u)) 0 = 0 ∧
      iteratedDeriv 2 (fun u : ℂ => centeredExponentialPhase S l (q,u)) 0 = -1 := by
    rintro x ⟨t,ht,rfl⟩
    filter_upwards [(hS t ht).eventually_analyticAt,hunit t ht] with q hq hu
    exact ⟨by simp [centeredExponentialPhase,centeredExponentialSlice],
      (centeredExponentialSlice_jets S q (Complex.I*l q) hq).2.1,
      centeredExponentialPhase_second S l q hq hu⟩
  obtain ⟨U,hU,hKU,rU,hrU,hPhase⟩ := compact_normalized_phase_quadratic_bound K hK
    (centeredExponentialPhase S l) hF hj
  obtain ⟨V,rV,C,hV,hKV,hrV,hC,hAf,hAb⟩ :=
    compact_premorse_family_of_fixed_coefficients P p a b ha hab hbc l Bc hl hBc
      Ωf f C0 B hΩf hcover hC0 hB hf hfr hfb
  refine ⟨U ∩ V,min rU rV,C,hU.inter hV,
    (fun x hx => ⟨hKU ⟨x,hx,rfl⟩,hKV x hx⟩),lt_min hrU hrV,hC,?_,?_⟩
  · intro j z hz
    apply hAf j z
    refine ⟨hz.1.2,?_⟩
    rw [Metric.mem_ball,dist_zero_right]
    exact (show ‖z.2‖ < min rU rV from by simpa only [Metric.mem_ball,dist_zero_right] using hz.2).trans_le (min_le_right _ _)
  · intro x hx u hu
    have h1 := hPhase x hx.1 u (hu.trans_le (min_le_left _ _))
    have h2 := hAb x hx.2 u (hu.trans_le (min_le_right _ _))
    exact ⟨h1.1,h1.2,h2.1,h2.2⟩
end WP.Analysis
