import WPFormalization.Volumes.CompactRawMorseMatching
import WPFormalization.Analysis.NormalizedMorseModelGevrey
import WPFormalization.Analysis.CompactGaussianPatching
/-! Uniform Gaussian remainder on a compact physical interval for the literal given finite marked model and the original CG3 numerator. Actual local Morse charts identify the original coefficients throughout each patch; a finite subcover then supplies common constants. The given S/l/Bc/f and Gevrey base B are preserved, as are the native J budget and every smaller cutoff. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology

lemma compact_original_numerator_uniform_gaussian_gevrey_two_all_cutoffs
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
    ∃ ρ A E : ℝ, 0 < ρ ∧ 0 < A ∧ 0 < E ∧
      ∀ τ ∈ Ioc (0 : ℝ) ρ, ∃ c rate H : ℝ, 0 < c ∧ 0 < rate ∧ 0 < H ∧
      ∀ x ∈ Icc a b, ∀ h : ℝ, H ≤ h → ∀ J K : ℕ, K ≤ J →
        2 * B * ((J : ℝ) + 1)^2 ≤ h → (K : ℝ) ≤ c * Real.sqrt h →
        ‖finiteMorseSourceIntegral (fun u : ℂ => centeredExponentialPhase S l ((x : ℂ),u))
            (fun s u => compactPremorseAmplitude P Bc l f s ((x : ℂ),u))
            h (τ / Real.sqrt (Real.sqrt h)) J -
          (Real.sqrt (2*Real.pi) : ℂ) * ∑ j ∈ Finset.range (K+1),
            ((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x) : ℝ) : ℂ) / (h : ℂ)^j‖ ≤
          A * E^(K+1) * ((K+1).factorial : ℝ)^2 / h^(K+1) +
            A * Real.exp (-rate*Real.sqrt h) := by
  let err : ℝ → ℝ → ℝ → ℕ → ℕ → ℝ := fun x τ h J K =>
    ‖finiteMorseSourceIntegral (fun u : ℂ => centeredExponentialPhase S l ((x : ℂ),u))
        (fun s u => compactPremorseAmplitude P Bc l f s ((x : ℂ),u))
        h (τ / Real.sqrt (Real.sqrt h)) J -
      (Real.sqrt (2*Real.pi) : ℂ) * ∑ j ∈ Finset.range (K+1),
        ((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x) : ℝ) : ℂ) / (h : ℂ)^j‖
  let budget : ℝ → ℕ → ℕ → Prop := fun h J _ => 2 * B * ((J : ℝ) + 1)^2 ≤ h
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Ioo (0 : ℝ) xCritical :=
    ⟨ha.trans_le hx.1, hx.2.trans_lt hbc⟩
  apply compact_gaussian_remainder_patching (Icc a b) isCompact_Icc err budget
  intro x0 hx0
  obtain ⟨d⟩ := exists_compact_morse_model_domain_at P p S l Bc x0 (hpoint x0 hx0)
    (hdata x0 hx0).1 (hdata x0 hx0).2.1 (hBc x0 ⟨(hpoint x0 hx0).1.le,(hpoint x0 hx0).2⟩).1
    (hBc x0 ⟨(hpoint x0 hx0).1.le,(hpoint x0 hx0).2⟩).2 (hdata x0 hx0).2.2.2.2
    Ω f C B hΩ hcover hC hB hf hbound
  obtain ⟨A,E,hA,hE,herror⟩ := d.gaussian_gevrey_two_all_cutoffs hB
  let U : Set ℝ := {x | ‖(x : ℂ) - (x0 : ℂ)‖ < d.rho}
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hxU : x0 ∈ U := by simpa only [U,mem_ofPred_eq,sub_self,norm_zero] using d.rho_pos
  refine ⟨U,d.rho,A,E,hU,hxU,d.rho_pos,hA,hE,?_⟩
  intro τ hτ
  obtain ⟨c,rate,H,hc,hrate,hH,he⟩ := herror τ hτ
  refine ⟨c,rate,H,hc,hrate,hH,?_⟩
  intro x hx h hh J K hKJ hbudget hK
  let δ : ℂ := (x : ℂ) - (x0 : ℂ)
  have hδ : ‖δ‖ < d.rho := hx.2
  have hadd : (x0 : ℂ) + δ = (x : ℂ) := by dsimp [δ]; ring
  have hnum := compact_raw_numerator_coefficients_of_domain P p hp S l Bc (x0 : ℂ) Ω f B
    hΩ hcover hf hfr hBc d δ hδ x (hpoint x hx.1) hadd
    (hdata x hx.1).1 (hdata x hx.1).2.2.1 (hdata x hx.1).2.2.2.1
    (hdata x hx.1).2.2.2.2.self_of_nhds
  have herr := he δ hδ h hh J K hKJ hbudget hK
  have hpoly : (∑ j ∈ Finset.range (K+1),
      gaussianModelCoefficient (fun s u => morseTransformedAmplitude
        (compactMorseBase Bc l x0) (compactMorseParameter P l x0) f d.U s (δ,u)) j / (h : ℂ)^j) =
      ∑ j ∈ Finset.range (K+1),
        ((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x) : ℝ) : ℂ) / (h : ℂ)^j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hnum j]
  rw [hpoly] at herr
  simpa only [err,compactMorsePhase,morseSourceAmplitude,compactMorseBase,
    compactMorseParameter,compactPremorseAmplitude,hadd] using herr
end WP.Analysis
