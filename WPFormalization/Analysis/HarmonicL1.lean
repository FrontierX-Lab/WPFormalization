import WPFormalization.Analysis.HarmonicGaussian
import WPFormalization.Analysis.GaussianEnvelope
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
noncomputable def scaledHarmonicFourier (Y:ℝ)(h:ℕ)(t:ℝ) : ℂ :=
  if |t|≤Real.pi*Real.sqrt (h:ℝ) then centeredHarmonic Y ((t/Real.sqrt (h:ℝ):ℝ):ℂ)^h else 0
noncomputable def harmonicGaussianKernel (Y t:ℝ) : ℂ :=
  Complex.exp (-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2)
noncomputable def geometricOuterEnvelope (ρ:ℝ)(h:ℕ)(t:ℝ) : ℝ :=
  if |t|≤Real.pi*Real.sqrt (h:ℝ) then ρ^h else 0
lemma harmonicVariance_pos (Y:ℝ)(hY:Y∈Icc 0 y₀) : 0<harmonicVariance Y := by
  obtain ⟨c,B,s,hc,hB,hs,hbound⟩ := harmonic_uniform_bounds
  exact lt_of_lt_of_le hc (hbound Y hY).2.2.1
lemma harmonicGaussianKernel_norm (Y t:ℝ) :
    ‖harmonicGaussianKernel Y t‖=Real.exp (-harmonicVariance Y/2*t^2) := by
  have he : -(harmonicVariance Y:ℂ)/2*(t:ℂ)^2 = ((-harmonicVariance Y/2*t^2:ℝ):ℂ) := by push_cast; rfl
  unfold harmonicGaussianKernel
  rw [he,Complex.norm_exp,Complex.ofReal_re]
lemma harmonicGaussianKernel_integrable (Y:ℝ)(hY:Y∈Icc 0 y₀) : Integrable (harmonicGaussianKernel Y) volume := by
  apply (integrable_exp_neg_mul_sq (half_pos (harmonicVariance_pos Y hY))).mono'
  · apply Continuous.aestronglyMeasurable
    change Continuous (fun t:ℝ=>Complex.exp (-(harmonicVariance Y:ℂ)/2*(t:ℂ)^2))
    fun_prop
  · apply ae_of_all
    intro t
    rw [harmonicGaussianKernel_norm]
    apply le_of_eq
    congr 1
    ring
lemma centeredHarmonic_continuous_real (Y:ℝ)(hY:Y∈Icc 0 y₀) : Continuous (fun t:ℝ=>centeredHarmonic Y t) := by
  have hmap : Continuous (fun t:ℝ=>(⟨Y,hY⟩,t):ℝ→Icc (0:ℝ) y₀ × ℝ) := continuous_const.prodMk continuous_id
  have hc : Continuous (fun t:ℝ=>harmonicCharacteristic Y t) := harmonicCharacteristic_joint_continuous.comp hmap
  have hp : Continuous (fun t:ℝ=>Complex.exp (-(3/2:ℂ)*(t:ℂ)*Complex.I)) := by fun_prop
  exact hp.mul hc
lemma scaledHarmonicFourier_indicator (Y:ℝ)(h:ℕ) : scaledHarmonicFourier Y h =
    (Icc (-(Real.pi*Real.sqrt (h:ℝ))) (Real.pi*Real.sqrt (h:ℝ))).indicator
      (fun t:ℝ=>centeredHarmonic Y ((t/Real.sqrt (h:ℝ):ℝ):ℂ)^h) := by
  ext t
  simp only [scaledHarmonicFourier,Set.indicator_apply,Set.mem_Icc,←abs_le]
lemma scaledHarmonicFourier_integrable (Y:ℝ)(hY:Y∈Icc 0 y₀)(h:ℕ) : Integrable (scaledHarmonicFourier Y h) volume := by
  have hc : Continuous (fun t:ℝ=>centeredHarmonic Y ((t/Real.sqrt (h:ℝ):ℝ):ℂ)^h) :=
    ((centeredHarmonic_continuous_real Y hY).comp (continuous_id.div_const _)).pow h
  rw [scaledHarmonicFourier_indicator]
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc
lemma geometricOuterEnvelope_integrable (ρ:ℝ)(h:ℕ) : Integrable (geometricOuterEnvelope ρ h) volume := by
  have he : geometricOuterEnvelope ρ h = (Icc (-(Real.pi*Real.sqrt (h:ℝ))) (Real.pi*Real.sqrt (h:ℝ))).indicator (fun _=>ρ^h) := by
    ext t
    simp only [geometricOuterEnvelope,Set.indicator_apply,Set.mem_Icc,←abs_le]
  rw [he]
  exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
lemma geometricOuterEnvelope_integral (ρ:ℝ)(h:ℕ) : ∫t:ℝ,geometricOuterEnvelope ρ h t=2*Real.pi*Real.sqrt (h:ℝ)*ρ^h := by
  have he : geometricOuterEnvelope ρ h = (Icc (-(Real.pi*Real.sqrt (h:ℝ))) (Real.pi*Real.sqrt (h:ℝ))).indicator (fun _=>ρ^h) := by
    ext t
    simp only [geometricOuterEnvelope,Set.indicator_apply,Set.mem_Icc,←abs_le]
  rw [he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by nlinarith [mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg (h:ℝ))] : -(Real.pi*Real.sqrt (h:ℝ))≤Real.pi*Real.sqrt (h:ℝ)),intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring
lemma geometricOuterEnvelope_integral_tendsto (ρ:ℝ)(hρ:0≤ρ)(hρ1:ρ<1) :
    Tendsto (fun h:ℕ=>∫t:ℝ,geometricOuterEnvelope ρ h t) atTop (𝓝 0) := by
  have ht := (sqrt_mul_geometric_tendsto ρ hρ hρ1).const_mul (2*Real.pi)
  simpa only [geometricOuterEnvelope_integral,mul_assoc,mul_zero] using ht
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma harmonicFourier_error_envelope : ∃δ C β γ ρ:ℝ,
    0<δ ∧ 0<C ∧ 0<β ∧ 0<γ ∧ 0≤ρ ∧ ρ<1 ∧ ∀Y∈Icc (0:ℝ) y₀,∀h:ℕ,0<h→∀t:ℝ,
      ‖scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t‖≤
        gaussianErrorEnvelope C β γ h t+geometricOuterEnvelope ρ h t+gaussianOuterTail δ γ h t := by
  obtain ⟨δE,C,hδE,hC,herror⟩ := centeredHarmonic_scaled_gaussian_error
  obtain ⟨δB,β,hδB,hβ,hbound⟩ := centeredHarmonic_scaled_gaussian_bound
  obtain ⟨c,B,s,hc,hB,hs,hvar⟩ := harmonic_uniform_bounds
  let δ := min δE (min δB Real.pi)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδπ : δ≤Real.pi := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ρ,hρ,hρ1,hgap⟩ := harmonicCharacteristic_uniform_gap δ hδ hδπ
  refine ⟨δ,C,β,c/2,ρ,hδ,hC,hβ,by positivity,hρ,hρ1,?_⟩
  intro Y hY h hh t
  let r := Real.sqrt (h:ℝ)
  let u : ℝ := t/r
  have hr : 0<r := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have huAbs : |u|=|t|/r := by dsimp [u]; rw [abs_div,abs_of_pos hr]
  have hG : ‖harmonicGaussianKernel Y t‖≤Real.exp (-(c/2)*t^2) := by
    rw [harmonicGaussianKernel_norm]
    apply Real.exp_le_exp.mpr
    have hv := (hvar Y hY).2.2.1
    nlinarith [mul_le_mul_of_nonneg_right hv (sq_nonneg t)]
  have hEnv : 0≤gaussianErrorEnvelope C β (c/2) h t := gaussianErrorEnvelope_nonneg C β (c/2) hC.le h t
  have hGeo : 0≤geometricOuterEnvelope ρ h t := by unfold geometricOuterEnvelope; split_ifs <;> positivity
  have hTail : 0≤gaussianOuterTail δ (c/2) h t := by unfold gaussianOuterTail; split_ifs <;> positivity
  by_cases hInner : |t|≤δ*r
  · have huδ : |u|≤δ := by rw [huAbs]; exact (div_le_iff₀ hr).mpr (by linarith)
    have hCut : |t|≤Real.pi*r := hInner.trans (mul_le_mul_of_nonneg_right hδπ hr.le)
    have hE := herror Y hY h hh t (huδ.trans (min_le_left _ _))
    have hB := hbound Y hY h hh t (huδ.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hsum : ‖centeredHarmonic Y (u:ℂ)^h-harmonicGaussianKernel Y t‖≤Real.exp (-β*t^2)+Real.exp (-(c/2)*t^2) :=
      (norm_sub_le _ _).trans (add_le_add hB hG)
    have hMin : ‖centeredHarmonic Y (u:ℂ)^h-harmonicGaussianKernel Y t‖≤gaussianErrorEnvelope C β (c/2) h t := by
      apply le_min
      · exact hE
      · exact hsum
    rw [scaledHarmonicFourier,if_pos hCut]
    nlinarith
  · have hOut : δ*r< |t| := lt_of_not_ge hInner
    have hTailEq : gaussianOuterTail δ (c/2) h t=Real.exp (-(c/2)*t^2) := by
      unfold gaussianOuterTail
      rw [if_pos hOut]
    by_cases hCut : |t|≤Real.pi*r
    · have huPi : u∈Icc (-Real.pi) Real.pi := by
        apply abs_le.mp
        rw [huAbs]
        exact (div_le_iff₀ hr).mpr (by linarith)
      have huδ : δ≤|u| := by rw [huAbs]; apply (le_div_iff₀ hr).mpr; linarith
      have hChar := hgap Y hY u huPi huδ
      have hPower : ‖centeredHarmonic Y (u:ℂ)^h‖≤ρ^h := by
        rw [norm_pow,centeredHarmonic_norm_real]
        exact pow_le_pow_left₀ (norm_nonneg _) hChar h
      have hsum := (norm_sub_le (centeredHarmonic Y (u:ℂ)^h) (harmonicGaussianKernel Y t)).trans (add_le_add hPower hG)
      rw [scaledHarmonicFourier,if_pos hCut,geometricOuterEnvelope,if_pos hCut,hTailEq]
      nlinarith
    · rw [scaledHarmonicFourier,if_neg hCut,zero_sub,norm_neg,hTailEq]
      nlinarith
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma real_fourier_phase_norm (q t:ℝ) : ‖Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)‖=1 := by
  rw [Complex.norm_exp]
  norm_num [Complex.mul_re,Complex.mul_im]
lemma real_fourier_phase_mul_integrable (q:ℝ)(f:ℝ→ℂ)(hf:Integrable f volume) :
    Integrable (fun t:ℝ=>Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*f t) volume := by
  apply hf.norm.mono'
  · have hp : Continuous (fun t:ℝ=>Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)) := by fun_prop
    exact hp.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · exact ae_of_all _ (fun t=>by simp only [norm_mul,real_fourier_phase_norm,one_mul,le_refl])
lemma harmonicFourier_uniform_l1_error : ∃a:ℕ→ℝ,(∀h,0≤a h) ∧ Tendsto a atTop (𝓝 0) ∧
    ∀Y∈Icc (0:ℝ) y₀,∀h:ℕ,0<h→∀q:ℝ,
      ‖∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*(scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t)‖≤a h := by
  obtain ⟨δ,C,β,γ,ρ,hδ,hC,hβ,hγ,hρ,hρ1,hpoint⟩ := harmonicFourier_error_envelope
  let a (h:ℕ) : ℝ := (∫t:ℝ,gaussianErrorEnvelope C β γ h t)+
    (∫t:ℝ,geometricOuterEnvelope ρ h t)+(∫t:ℝ,gaussianOuterTail δ γ h t)
  have hI (h:ℕ) := gaussianErrorEnvelope_integrable C β γ hC.le hβ hγ h
  have hO (h:ℕ) := geometricOuterEnvelope_integrable ρ h
  have hT (h:ℕ) := gaussianOuterTail_integrable δ γ hγ h
  refine ⟨a,?_,?_,?_⟩
  · intro h
    apply add_nonneg (add_nonneg (integral_nonneg (gaussianErrorEnvelope_nonneg C β γ hC.le h)) ?_) ?_
    · apply integral_nonneg
      intro t
      unfold geometricOuterEnvelope
      split_ifs <;> positivity
    · apply integral_nonneg
      intro t
      unfold gaussianOuterTail
      split_ifs <;> positivity
  · have ht := ((gaussianErrorEnvelope_integral_tendsto C β γ hC.le hβ hγ).add
      (geometricOuterEnvelope_integral_tendsto ρ hρ hρ1)).add (gaussianOuterTail_integral_tendsto δ γ hδ hγ)
    simpa only [add_zero] using ht
  · intro Y hY h hh q
    have hdiff := ((scaledHarmonicFourier_integrable Y hY h).sub (harmonicGaussianKernel_integrable Y hY)).norm
    have hsum := ((hI h).add (hO h)).add (hT h)
    calc ‖∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*(scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t)‖
          ≤ ∫t:ℝ,‖Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*(scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t)‖ := norm_integral_le_integral_norm _
         _ = ∫t:ℝ,‖scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t‖ := by
          apply integral_congr_ae
          exact ae_of_all _ (fun t=>by simp only [norm_mul,real_fourier_phase_norm,one_mul,le_refl])
         _ ≤ ∫t:ℝ,gaussianErrorEnvelope C β γ h t+geometricOuterEnvelope ρ h t+gaussianOuterTail δ γ h t :=
          integral_mono_ae hdiff hsum (ae_of_all _ (hpoint Y hY h hh))
         _ = a h := by
          have h1 := integral_add (hI h) (hO h)
          have h2 := integral_add ((hI h).add (hO h)) (hT h)
          simp only [Pi.add_apply] at h2
          rw [h2,h1]
end WP.Analysis
