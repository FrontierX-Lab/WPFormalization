import WPFormalization.Volumes.RawMorseMatching
import WPFormalization.Analysis.ExtractionDenominatorRegrading
/-! The original rawExtractedCoefficient has exactly the genuine normalized Morse numerator and the inverse original Poisson Stirling convolution. This is a proved coefficient identity, separate from uniform extraction error bounds. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma actual_raw_extraction_morse_product (P:PsiTheory) (p:ℕ) (hp:1≤p) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) :
    ∃(S B:ℂ→ℂ)(Γ:ℕ→ℂ→ℂ)(U:ℂ→ℂ),
      AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ B (x:ℂ) ∧
      ((fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ))) ∧
      ((fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ))) ∧
      (∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
        (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
          (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ))) ∧
      AnalyticAt ℂ U 0 ∧ U 0=0 ∧ deriv U 0=1 ∧
      (∀ᶠz:ℂ in 𝓝 0,extractionStationaryPhase S x (U z)=-z^2/2) ∧
      ∀j:ℕ,(HigherOrder.rawExtractedCoefficient P p j (inverseY x):ℂ)=
        ∑i∈Finset.range (j+1),gaussianModelCoefficient (extractionMorseGermAmplitude B Γ x U) i*
          ((PowerSeries.coeff (j-i) (HigherOrder.poissonStirlingSeries⁻¹):ℝ):ℂ)/(WP.Psi x:ℂ)^(j-i) := by
  obtain ⟨S,B,Γ,U,hS,hB,hSr,hBr,hΓ,hU,hU0,hUd,hphase,hnum⟩:=
    actual_raw_gaussian_numerator_morse_identity P p hp x hx
  refine ⟨S,B,Γ,U,hS,hB,hSr,hBr,hΓ,hU,hU0,hUd,hphase,?_⟩
  intro j
  have he:=raw_extraction_complex_morse_convolution P p hp x hx j
    (gaussianModelCoefficient (extractionMorseGermAmplitude B Γ x U)) (fun i hi=>hnum i)
  change ((PowerSeries.coeff (2*j)
    (HigherOrder.extractionNumerator P p (XR (inverseY x))*(HigherOrder.extractionDenominator (XR (inverseY x)))⁻¹):ℝ):ℂ)=_
  rw[(inverseY_branch x ⟨hx.1.le,hx.2⟩).2]
  exact he
end WP.Analysis
