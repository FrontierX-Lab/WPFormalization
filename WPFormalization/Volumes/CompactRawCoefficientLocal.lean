import WPFormalization.Volumes.JointCompactMorseDomain
import WPFormalization.Volumes.CompactRawMorseMatching
import WPFormalization.Volumes.CriticalGaussianModel
import WPFormalization.Analysis.ScaledSeriesConvolution
import WPFormalization.Analysis.PoissonNormalizer
/-! The ORIGINAL raw CG3 coefficients have one holomorphic Gevrey-two family near each compact physical x-axis point. A genuinely joint Morse amplitude family supplies parameter analyticity and Cauchy bounds; the true reciprocal Euler mean supplies the inverse-Poisson convolution. Actual neighboring real traces identify the original coefficient recipe at every order. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
set_option maxHeartbeats 1500000 in
lemma compact_raw_coefficient_local_x_extension (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (hβc : β < xCritical)
    (S l Bc : ℂ → ℂ) (Ω : Set ℂ) (f : ℕ → ℂ → ℂ) (C B : ℝ)
    (hΩ : IsOpen Ω) (hcover : ∀ Y ∈ Icc (0 : ℝ) y₀, (Y : ℂ) ∈ Ω)
    (hC : 0 < C) (hB : 0 < B) (hf : ∀ j, AnalyticOnNhd ℂ (f j) Ω)
    (hfr : ∀ j Y, Y ∈ Icc (0 : ℝ) y₀ → f j (Y : ℂ) = (HigherOrder.markedCoefficient P p j Y : ℂ))
    (hbound : ∀ j z, z ∈ Ω → ‖f j z‖ ≤ C * B^j * (j.factorial : ℝ)^2)
    (hdata : ∀ x ∈ Icc α β, AnalyticAt ℂ S (x : ℂ) ∧ AnalyticAt ℂ l (x : ℂ) ∧
      ((fun t : ℝ => S (t : ℂ)) =ᶠ[𝓝 x] (fun t : ℝ => (extractionS t : ℂ))) ∧
      l (x : ℂ) = ((Real.sqrt (WP.euler WP.Psi x))⁻¹ : ℝ) ∧
      ∀ᶠ q : ℂ in 𝓝 (x : ℂ), (l q)^2 * ((complexEuler^[2]) S) q = 1)
    (hν : ∀ x ∈ Icc α β, complexEuler S (x : ℂ) = (WP.Psi x : ℂ))
    (hBc : ∀ x ∈ Ico (0 : ℝ) xCritical, AnalyticAt ℂ Bc (x : ℂ) ∧ Bc (x : ℂ) = (extractionB p x : ℂ))
    (x0 : ℝ) (hx0 : x0 ∈ Icc α β) :
    ∃ (F : ℕ → ℂ → ℂ) (R Cr Br : ℝ), 0 < R ∧ 0 < Cr ∧ 0 < Br ∧
      (∀ j, AnalyticOnNhd ℂ (F j) (Metric.ball 0 R)) ∧
      (∀ j z, ‖z‖ < R → ‖F j z‖ ≤ Cr * Br^j * (j.factorial : ℝ)^2) ∧
      ∀ x ∈ Icc α β, |x-x0| < R → ∀ j,
        F j ((x-x0 : ℝ) : ℂ) = (HigherOrder.rawExtractedCoefficient P p j (inverseY x) : ℂ) := by
  have hphysical (x : ℝ) (hx : x ∈ Icc α β) : x ∈ Ioo (0 : ℝ) xCritical :=
    ⟨hα.trans_le hx.1,hx.2.trans_lt hβc⟩
  obtain ⟨d,hjoint⟩ := exists_joint_compact_morse_model_domain_at P p S l Bc x0 (hphysical x0 hx0)
    (hdata x0 hx0).1 (hdata x0 hx0).2.1
    (hBc x0 ⟨(hphysical x0 hx0).1.le,(hphysical x0 hx0).2⟩).1
    (hBc x0 ⟨(hphysical x0 hx0).1.le,(hphysical x0 hx0).2⟩).2
    (hdata x0 hx0).2.2.2.2 Ω f C B hΩ hcover hC hB hf hbound
  let H : ℕ → ℂ × ℂ → ℂ := fun s => morseTransformedAmplitude
    (compactMorseBase Bc l x0) (compactMorseParameter P l x0) f d.U s
  let G : ℕ → ℂ → ℂ := fun j δ => gaussianModelCoefficient (fun s u => H s (δ,u)) j
  let Bg : ℝ := 2 * max B (2/d.R^2)
  have hBg : 0 < Bg := mul_pos (by norm_num) (hB.trans_le (le_max_left _ _))
  have hGa (j : ℕ) : AnalyticOnNhd ℂ (G j) (Metric.ball 0 d.rho) := by
    intro δ hδ
    exact gaussian_model_coefficient_parameter_analyticAt H δ j
      (fun s => hjoint s (δ,0) ⟨hδ,Metric.mem_ball_self d.R_pos⟩)
  have hGb (j : ℕ) (δ : ℂ) (hδ : ‖δ‖ < d.rho) :
      ‖G j δ‖ ≤ d.D * Bg^j * (j.factorial : ℝ)^2 :=
    gaussian_model_coefficients_gevrey_two (fun s u => H s (δ,u)) d.D B d.R d.D_pos.le hB.le d.R_pos
      (d.post_diff δ hδ) (fun s u hu => d.bound δ hδ s u (Metric.sphere_subset_closedBall hu)) j
  have hY0 := (inverseY_branch x0 ⟨(hphysical x0 hx0).1.le,(hphysical x0 hx0).2⟩).1
  have hY0p : 0 < inverseY x0 := by
    by_contra hn
    have he : inverseY x0 = 0 := le_antisymm (le_of_not_gt hn) hY0.1
    have he' := (inverseY_branch x0 ⟨(hphysical x0 hx0).1.le,(hphysical x0 hx0).2⟩).2
    rw [he,XR_zero] at he'
    linarith [(hphysical x0 hx0).1]
  have hP0 : 0 < WP.Psi x0 := by
    have he := density_strictMonoOn ⟨le_rfl,y₀_pos⟩ hY0 hY0p
    rw [density_zero_value] at he
    exact half_pos he
  let T : ℂ → ℂ := fun δ => (complexEuler S ((x0 : ℂ)+δ))⁻¹
  have hT : AnalyticAt ℂ T 0 := by
    apply ((complexEuler_analyticAt S (x0 : ℂ) (hdata x0 hx0).1).comp_of_eq
      (analyticAt_const.add analyticAt_id) (by simp)).inv
    change complexEuler S ((x0 : ℂ)+0) ≠ 0
    rw [add_zero,hν x0 hx0]
    exact_mod_cast hP0.ne'
  let M : ℝ := ‖T 0‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMb : ∀ᶠ δ : ℂ in 𝓝 0, ‖T δ‖ ≤ M :=
    (hT.continuousAt.norm.tendsto.eventually (eventually_lt_nhds (by dsimp [M]; linarith))).mono (fun δ hδ => hδ.le)
  have hgood : ∀ᶠ δ : ℂ in 𝓝 0, AnalyticAt ℂ T δ ∧ ‖T δ‖ ≤ M :=
    hT.eventually_analyticAt.and hMb
  obtain ⟨Rt,hRt,hTa⟩ := Metric.eventually_nhds_iff.mp hgood
  let R : ℝ := min d.rho Rt / 2
  have hR : 0 < R := half_pos (lt_min d.rho_pos hRt)
  have hRρ : R < d.rho := (half_lt_self (lt_min d.rho_pos hRt)).trans_le (min_le_left _ _)
  have hRRt : R < Rt := (half_lt_self (lt_min d.rho_pos hRt)).trans_le (min_le_right _ _)
  obtain ⟨Cp,Bp,hCp,hBp,hcb⟩ := GevreyOneAsymptotic.coeff_bound
    (fun x => (poissonNormalizer x)⁻¹) (HigherOrder.poissonStirlingSeries⁻¹) poissonNormalizer_inv_gevrey_one
  let c : ℕ → ℝ := fun j => PowerSeries.coeff j (HigherOrder.poissonStirlingSeries⁻¹)
  let F : ℕ → ℂ → ℂ := scaledSeriesConvolution G c T
  let Br : ℝ := 2 * max Bg (Bp*M)
  have hBr : 0 < Br := mul_pos (by norm_num) (hBg.trans_le (le_max_left _ _))
  have hGaR (j : ℕ) : AnalyticOnNhd ℂ (G j) (Metric.ball 0 R) :=
    (hGa j).mono (Metric.ball_subset_ball hRρ.le)
  have hTaR : AnalyticOnNhd ℂ T (Metric.ball 0 R) := by
    intro z hz
    exact (hTa (show dist z 0 < Rt from
      (show dist z 0 < R from hz).trans hRRt)).1
  refine ⟨F,R,d.D*Cp,Br,hR,mul_pos d.D_pos hCp,hBr,
    (fun j => scaledSeriesConvolution_analyticOnNhd G c T _ hGaR hTaR j),?_,?_⟩
  · intro j z hz
    exact scaledSeriesConvolution_gevreyTwo_bound G c T d.D Bg Cp Bp M d.D_pos.le hBg.le
      hCp.le hBp.le hM.le z (fun i => hGb i z (hz.trans hRρ)) hcb
      (hTa (by rw [dist_zero_right]; exact hz.trans hRRt)).2 j
  · intro x hx hxr j
    let δ : ℂ := ((x-x0 : ℝ) : ℂ)
    have hδR : ‖δ‖ < R := by rw [Complex.norm_real,Real.norm_eq_abs]; exact hxr
    have hδ : ‖δ‖ < d.rho := hδR.trans hRρ
    have hadd : (x0 : ℂ)+δ=(x : ℂ) := by dsimp [δ]; push_cast; ring
    have hnum := compact_raw_numerator_coefficients_of_domain P p hp S l Bc (x0 : ℂ) Ω f B
      hΩ hcover hf hfr hBc d δ hδ x (hphysical x hx) hadd
      (hdata x hx).1 (hdata x hx).2.2.1 (hdata x hx).2.2.2.1 (hdata x hx).2.2.2.2.self_of_nhds
    have hconv := raw_extraction_complex_morse_convolution P p hp x (hphysical x hx) j
      (fun i => G i δ) (fun i hi => hnum i)
    have hraw : HigherOrder.rawExtractedCoefficient P p j (inverseY x) =
        PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x*(HigherOrder.extractionDenominator x)⁻¹) := by
      unfold HigherOrder.rawExtractedCoefficient
      rw [(inverseY_branch x ⟨(hphysical x hx).1.le,(hphysical x hx).2⟩).2]
    have hTx : T δ = (WP.Psi x : ℂ)⁻¹ := by dsimp only [T]; rw [hadd,hν x hx]
    rw [hraw,hconv]
    dsimp only [F,scaledSeriesConvolution,c]
    rw [hTx]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [δ]
    push_cast
    simp only [inv_pow,div_eq_mul_inv]
end WP.Analysis
