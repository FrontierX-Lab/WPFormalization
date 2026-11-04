import WPFormalization.Volumes.RawMorseMatching
import WPFormalization.Analysis.ExtractionDenominatorRegrading
import WPFormalization.Volumes.CriticalPhasePhysicalGerm
import WPFormalization.Volumes.CriticalMorseFibers
import WPFormalization.Volumes.CriticalAmplitudePhysicalGerm
/-! The prescribed original CG3 coefficients equal the Gaussian coefficients of the same actual joint critical model. The coordinate d.U and canonical Q/f family are retained. Physical complex germs, common Morse fibers and proved real-integral uniqueness supply the identity at every order. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma gaussian_model_coefficient_congr_germs (F G:ℕ→ℂ→ℂ) (j:ℕ)
    (hFG:∀s≤j,F s=ᶠ[𝓝 0] G s) :gaussianModelCoefficient F j=gaussianModelCoefficient G j := by
  unfold gaussianModelCoefficient
  apply Finset.sum_congr rfl
  intro s hs
  rw[coeff_congr_of_eventuallyEq _ _ (hFG s (Nat.le_of_lt_succ (Finset.mem_range.mp hs)))]

lemma CriticalGaussianCoordinateData.original_raw_coefficients_eq_critical_model
    (d:CriticalGaussianCoordinateData) (P:PsiTheory) (p:ℕ) (hp:1≤p)
    (Q:ℂ→ℂ) (f:ℕ→ℂ→ℂ) (Ω:Set ℂ) (hΩ:IsOpen Ω) (hcover:(y₀:ℂ)∈Ω)
    (hQa:AnalyticAt ℂ Q 0) (hQ0:Q 0=1)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ))
    (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hfr:∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ)) :
    ∃R:ℝ,0<R ∧ R<y₀ ∧ ∀δ∈Ioo (0:ℝ) R,∀j:ℕ,
      ((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p (XR (y₀-δ))):ℝ):ℂ)=
        gaussianModelCoefficient (fun s u=>d.modelAmplitude Q p f s ((δ:ℂ),u)) j ∧
      (HigherOrder.rawExtractedCoefficient P p j (y₀-δ):ℂ)=
        ∑i∈Finset.range (j+1),gaussianModelCoefficient (fun s u=>d.modelAmplitude Q p f s ((δ:ℂ),u)) i*
          ((PowerSeries.coeff (j-i) (HigherOrder.poissonStirlingSeries⁻¹):ℝ):ℂ)/(WP.Psi (XR (y₀-δ)):ℂ)^(j-i) := by
  obtain ⟨Rp,hRp,hRpy,hPhase⟩:=d.centeredPhase_germ_of_physical_action P Q p hQphys
  obtain ⟨Ra,hRa,hRay,hPost⟩:=d.modelAmplitude_germ_of_physical_amplitudes P p Q f hQa hQ0 hQphys Ω hΩ hcover hf hfr
  obtain ⟨W,Rw,C,hRw,hC,hFibers⟩:=d.exists_morse_fibers
  let R:ℝ:=min Rp (min Ra Rw)
  have hR:0<R:=lt_min hRp (lt_min hRa hRw)
  have hRRp:R≤Rp:=min_le_left _ _
  have hRRa:R≤Ra:=(min_le_right _ _).trans (min_le_left _ _)
  have hRRw:R≤Rw:=(min_le_right _ _).trans (min_le_right _ _)
  have hRy:R<y₀:=hRRp.trans_lt hRpy
  refine ⟨R,hR,hRy,?_⟩
  intro δ hδ
  let x:ℝ:=XR (y₀-δ)
  have hYp:0<y₀-δ:=by linarith[hδ.2]
  have hYlt:y₀-δ<y₀:=by linarith[hδ.1]
  have hx:x∈Ioo (0:ℝ) xCritical := by
    constructor
    · have hh:=XR_strictMonoOn (show (0:ℝ)∈Iic y₀ from y₀_pos.le)
        (show y₀-δ∈Iic y₀ from hYlt.le) hYp
      simpa only[XR_zero] using hh
    · exact XR_strictMonoOn (show y₀-δ∈Iic y₀ from hYlt.le) (show y₀∈Iic y₀ from by simp) hYlt
  obtain ⟨S,B,β,hS,hB,hSr,hBr,hvar,hβ,hβ0,hfac⟩:=exists_actual_extraction_log_data P p x hx
  obtain ⟨Γ,hΓ⟩:=canonical_marked_weight_germ_family P p hp x hx
  have hSrA:AnalyticAt ℝ extractionS x:=analyticAt_real_of_complex_trace S extractionS x hS hSr
  have hν:complexEuler S (x:ℂ)=(WP.Psi x:ℂ) := by
    have he:=iterated_complexEuler_real_trace S extractionS x hS hSrA hSr 1
    simp only[Function.iterate_one] at he
    have he1:WP.euler extractionS x=WP.Psi x:=extractionS_euler_eq_Psi x hx
    rw[he1] at he
    exact he
  have hδp:δ∈Ioo (0:ℝ) Rp:=⟨hδ.1,hδ.2.trans_le hRRp⟩
  have hδa:δ∈Ioo (0:ℝ) Ra:=⟨hδ.1,hδ.2.trans_le hRRa⟩
  have hδw:‖(δ:ℂ)‖<Rw:=by rw[Complex.norm_of_nonneg hδ.1.le];exact hδ.2.trans_le hRRw
  obtain ⟨hU,hW,hU0,hConj,hclose⟩:=hFibers (δ:ℂ) hδw
  have hPre: (fun u:ℂ=>d.kernel.centeredPhase d.L d.q ((δ:ℂ),u))=ᶠ[𝓝 0]
      extractionStationaryPhase S x :=hPhase δ hδp S hS hSr hν
  have ht:Tendsto (fun u:ℂ=>d.U ((δ:ℂ),u)) (𝓝 0) (𝓝 0) := by
    simpa only[hU0] using hU.continuousAt.tendsto
  have hConjS:∀ᶠu:ℂ in 𝓝 0,d.U ((δ:ℂ),W ((δ:ℂ),u))=u ∧
      extractionStationaryPhase S x (d.U ((δ:ℂ),u))=-u^2/2 := by
    filter_upwards[hConj,ht.eventually hPre] with u hu he
    exact ⟨hu.1,he.symm.trans hu.2⟩
  have hPost':∀s,(fun u:ℂ=>d.modelAmplitude Q p f s ((δ:ℂ),u))=ᶠ[𝓝 0]
      extractionMorseGermAmplitude B Γ x (fun u:ℂ=>d.U ((δ:ℂ),u)) s:=
    hPost δ hδa B Γ hB hBr hΓ
  have hNum(j:ℕ):((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)=
      gaussianModelCoefficient (fun s u=>d.modelAmplitude Q p f s ((δ:ℂ),u)) j := by
    have he:=raw_numerator_morse_coefficients_of_physical_germs P p hp x hx S B β Γ
      (fun u:ℂ=>d.U ((δ:ℂ),u)) (fun u:ℂ=>W ((δ:ℂ),u)) hS hB hSr hBr hvar hβ hβ0 hfac hΓ
      hU hW hU0 hConjS Rw C hRw hC hclose j j le_rfl
    exact he.trans (gaussian_model_coefficient_congr_germs _ _ j (fun s hs=>hPost' s)).symm
  intro j
  refine ⟨hNum j,?_⟩
  exact rawExtractedCoefficient_complex_morse_convolution P p hp (y₀-δ) hx j
    (gaussianModelCoefficient (fun s u=>d.modelAmplitude Q p f s ((δ:ℂ),u))) (fun i hi=>hNum i)
end WP.Analysis
