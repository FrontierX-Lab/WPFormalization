import WPFormalization.Volumes.CompactMorseDomain
import WPFormalization.Volumes.CriticalRawCoefficientMatching
/-! The original CG3 numerator equals the Gaussian coefficients of each given local compact Morse domain. The same S/l/Bc/f and local U/W are retained. Actual logarithmic amplitude and canonical planar-inverse germs supply the previously proved raw-integral matching; no extraction expansion is assumed. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology

lemma compact_raw_numerator_coefficients_of_domain (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (S l Bc : ℂ → ℂ) (x0 : ℂ) (Ω : Set ℂ) (f : ℕ → ℂ → ℂ) (B : ℝ)
    (hΩ : IsOpen Ω) (hcover : ∀ Y ∈ Icc (0 : ℝ) y₀, (Y : ℂ) ∈ Ω)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) Ω)
    (hfr : ∀ j Y, Y ∈ Icc (0 : ℝ) y₀ → f j (Y : ℂ) =
      (HigherOrder.markedCoefficient P p j Y : ℂ))
    (hBc : ∀ x ∈ Ico (0 : ℝ) xCritical,
      AnalyticAt ℂ Bc (x : ℂ) ∧ Bc (x : ℂ) = (extractionB p x : ℂ))
    (d : NormalizedMorseModelDomain (compactMorsePhase S l x0)
      (compactMorseBase Bc l x0) (compactMorseParameter P l x0) f B)
    (δ : ℂ) (hδ : ‖δ‖ < d.rho) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) xCritical)
    (hpoint : x0 + δ = (x : ℂ))
    (hS : AnalyticAt ℂ S (x : ℂ))
    (hSr : (fun t : ℝ => S (t : ℂ)) =ᶠ[𝓝 x] (fun t : ℝ => (extractionS t : ℂ)))
    (hl : l (x : ℂ) = ((Real.sqrt (WP.euler WP.Psi x))⁻¹ : ℝ))
    (hunit : (l (x : ℂ))^2 * ((complexEuler^[2]) S) (x : ℂ) = 1) :
    ∀ j : ℕ,
      ((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x) : ℝ) : ℂ) =
        gaussianModelCoefficient (fun s u => morseTransformedAmplitude
          (compactMorseBase Bc l x0) (compactMorseParameter P l x0) f d.U s (δ,u)) j := by
  let Blog : ℂ → ℂ := fun z => Complex.log (Bc z)
  let Γ : ℕ → ℂ → ℂ := fun j z => f j (PositiveConvolution.planarInverse P z)
  let c : ℂ := Complex.I / (Real.sqrt (WP.euler WP.Psi x) : ℂ)
  let arg : ℂ → ℂ := fun u => (x : ℂ) * Complex.exp (c*u)
  have hBcx := (hBc x ⟨hx.1.le, hx.2⟩).1
  have hBcxr := (hBc x ⟨hx.1.le, hx.2⟩).2
  have hBcn : Bc (x : ℂ) ≠ 0 := by
    rw [hBcxr]
    exact_mod_cast (extractionB_pos_interior p x ⟨hx.1.le, hx.2⟩).ne'
  have hBlog : AnalyticAt ℂ Blog (x : ℂ) := hBcx.clog (by
    rw [hBcxr]
    exact Or.inl (extractionB_pos_interior p x ⟨hx.1.le, hx.2⟩))
  have hBlogr : (fun t : ℝ => Blog (t : ℂ)) =ᶠ[𝓝 x]
      (fun t : ℝ => (Real.log (extractionB p t) : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    dsimp only [Blog]
    rw [(hBc t ⟨ht.1.le, ht.2⟩).2,
      ←Complex.ofReal_log (extractionB_pos_interior p t ⟨ht.1.le, ht.2⟩).le]
  have hxN : ‖(x : ℂ)‖ < xCritical := by
    rw [Complex.norm_of_nonneg hx.1.le]
    exact hx.2
  have hY := (inverseY_branch x ⟨hx.1.le, hx.2⟩).1
  have hΓ : ∀ s, AnalyticAt ℂ (Γ s) (x : ℂ) ∧
      (fun t : ℝ => Γ s (t : ℂ)) =ᶠ[𝓝 x]
        (fun t : ℝ => (HigherOrder.markedCoefficient P p s (inverseY t) : ℂ)) := by
    intro s
    constructor
    · have hpi := PositiveConvolution.planarInverse_analyticAt P (x : ℂ) hxN
      have hpi0 := PositiveConvolution.planarInverse_ofReal P x ⟨hx.1.le, hx.2⟩
      exact (hf s _ (by rw [hpi0]; exact hcover _ ⟨hY.1, hY.2.le⟩)).comp hpi
    · filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
      dsimp only [Γ]
      rw [PositiveConvolution.planarInverse_ofReal P t ⟨ht.1.le, ht.2⟩]
      have hy := (inverseY_branch t ⟨ht.1.le, ht.2⟩).1
      exact hfr s _ ⟨hy.1, hy.2.le⟩
  have hvar : 0 < WP.euler WP.Psi x := mul_pos hx.1
    (Psi_deriv_pos_interior x ⟨hx.1.le, hx.2⟩)
  have hphaseEq : (fun u : ℂ => compactMorsePhase S l x0 (δ,u)) = extractionStationaryPhase S x := by
    funext u
    dsimp only [compactMorsePhase, centeredExponentialPhase, extractionStationaryPhase]
    rw [hpoint, hl, Complex.ofReal_inv]
    congr 1
  let φ : ℂ → ℂ := extractionStationaryPhase S x
  have harg : AnalyticAt ℂ arg 0 := by fun_prop
  have harg0 : arg 0 = (x : ℂ) := by simp [arg]
  have hφ : AnalyticAt ℂ φ 0 :=
    (((hS.comp_of_eq harg harg0).sub analyticAt_const).sub (by fun_prop))
  have hjets := centeredExponentialSlice_jets S (x : ℂ) c hS
  have hφ2 : iteratedDeriv 2 φ 0 = -1 := by
    dsimp only [φ]
    rw [←hphaseEq]
    change iteratedDeriv 2 (fun u : ℂ => centeredExponentialPhase S l (x0+δ,u)) 0 = -1
    rw [hpoint]
    exact centeredExponentialPhase_second S l x hS hunit
  obtain ⟨G,hG,hG0,hfac0⟩ := complex_analytic_quadratic_factor φ hφ hjets.1 hjets.2.1
  let β : ℂ → ℂ := fun u => G u + (1/2 : ℂ)
  have hβ : AnalyticAt ℂ β 0 := hG.add analyticAt_const
  have hβ0 : β 0 = 0 := by dsimp only [β]; rw [hG0,hφ2]; ring
  have hfac : extractionStationaryPhase S x =ᶠ[𝓝 0]
      (fun u : ℂ => u^2*(β u-(1/2 : ℂ))) := by
    filter_upwards [hfac0] with u hu
    change φ u = u^2*(G u+(1/2 : ℂ)-(1/2 : ℂ))
    rw [hu]
    ring
  have hsrc (s : ℕ) :
      (fun u : ℂ => morseSourceAmplitude (compactMorseBase Bc l x0)
        (compactMorseParameter P l x0) f s (δ,u)) =ᶠ[𝓝 0]
      extractionPremorseGermAmplitude Blog Γ x s := by
    have ht : Tendsto arg (𝓝 0) (𝓝 (x : ℂ)) := by
      simpa only [harg0] using harg.continuousAt.tendsto
    filter_upwards [ht.eventually (hBcx.continuousAt.eventually_ne hBcn)] with u hu
    have hargEq : compactModelPoint l (x0+δ,u) = arg u := by
      dsimp only [compactModelPoint, arg, c]
      rw [hpoint,hl,Complex.ofReal_inv]
      congr 2
    dsimp only [morseSourceAmplitude, compactMorseBase, compactMorseParameter,
      extractionPremorseGermAmplitude, Blog, Γ]
    rw [hargEq,hpoint,Complex.exp_sub,Complex.exp_log hu,Complex.exp_log hBcn]
  obtain ⟨hU,hW,hU0,hW0,hUD⟩ := d.fibers δ hδ
  have htU : Tendsto (fun u : ℂ => d.U (δ,u)) (𝓝 0) (𝓝 0) := by
    simpa only [hU0] using hU.continuousAt.tendsto
  have hpost (s : ℕ) :
      (fun u : ℂ => morseTransformedAmplitude (compactMorseBase Bc l x0)
        (compactMorseParameter P l x0) f d.U s (δ,u)) =ᶠ[𝓝 0]
      extractionMorseGermAmplitude Blog Γ x (fun u : ℂ => d.U (δ,u)) s := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) d.R_pos, htU.eventually (hsrc s)] with u hu he
    dsimp only [extractionMorseGermAmplitude]
    rw [←d.transform δ hδ s u hu, he]
  have hconj : ∀ᶠ u : ℂ in 𝓝 0, d.U (δ,d.W (δ,u)) = u ∧
      extractionStationaryPhase S x (d.U (δ,u)) = -u^2/2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) d.rho_pos,
      Metric.ball_mem_nhds (0 : ℂ) d.R_pos] with u hu hv
    have hu' : ‖u‖ ≤ d.rho := by
      exact (show ‖u‖ < d.rho from by simpa only [Metric.mem_ball,dist_zero_right] using hu).le
    refine ⟨(d.W_control δ hδ u hu').2,?_⟩
    rw [←hphaseEq]
    exact d.quadratic δ hδ u hv
  intro j
  have he := raw_numerator_morse_coefficients_of_physical_germs P p hp x hx S Blog β Γ
    (fun u : ℂ => d.U (δ,u)) (fun u : ℂ => d.W (δ,u)) hS hBlog hSr hBlogr
    hvar hβ hβ0 hfac hΓ hU hW hU0 hconj d.rho d.Cw d.rho_pos d.Cw_pos
    (fun z hz => (d.W_control δ hδ z hz.le).1) j j le_rfl
  exact he.trans (gaussian_model_coefficient_congr_germs _ _ j (fun s hs => hpost s)).symm
end WP.Analysis
