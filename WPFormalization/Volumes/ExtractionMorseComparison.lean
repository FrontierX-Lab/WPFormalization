import WPFormalization.Analysis.FixedMorseModel
import WPFormalization.Volumes.ExtractionLogData
import WPFormalization.Analysis.MarkedTaylorPolynomialJets
/-! The actual extraction action and canonical marked amplitudes supply the exact finite Morse model comparison. For each fixed finite amplitude cutoff, every sufficiently small spatial cutoff and every real h>=1 are controlled by a genuine exponential connector error. The original CG3 coefficient equality is not asserted here. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma actual_extraction_stationary_morse_germs (P:PsiTheory) (p:ℕ) (hp:1≤p) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) :
    ∃(S B β:ℂ→ℂ)(Γ:ℕ→ℂ→ℂ)(U W:ℂ→ℂ),
      AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ B (x:ℂ) ∧
      ((fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ))) ∧
      ((fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ))) ∧
      0<WP.euler WP.Psi x ∧ AnalyticAt ℂ β 0 ∧ β 0=0 ∧
      (centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))=ᶠ[𝓝 0]
        (fun u:ℂ=>u^2*(β u-(1/2:ℂ)))) ∧
      (∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
        (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
          (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ))) ∧
      AnalyticAt ℂ U 0 ∧ AnalyticAt ℂ W 0 ∧ U 0=0 ∧ W 0=0 ∧ deriv U 0=1 ∧ deriv W 0=1 ∧
      (∀ᶠz:ℂ in 𝓝 0,U (W z)=z ∧ W (U z)=z ∧
        centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ)) (U z)=-z^2/2) ∧
      ∃ρ C:ℝ,0<ρ ∧ 0<C ∧ ∀z:ℂ,‖z‖<ρ→
        ‖U z-z‖≤C*‖z‖^2 ∧ ‖W z-z‖≤C*‖z‖^2 := by
  obtain ⟨S,B,β,hS,hB,hSr,hBr,hvar,hβ,hβ0,hfac⟩:=exists_actual_extraction_log_data P p x hx
  obtain ⟨Γ,hΓ⟩:=canonical_marked_weight_germ_family P p hp x hx
  obtain ⟨U,W,hU,hW,hU0,hW0,hUd,hWd,hconj,ρ,C,hρ,hC,hclose⟩:=exists_stationary_morse_germs β hβ hβ0
  have ht:Tendsto U (𝓝 0) (𝓝 0):=by simpa only[hU0] using hU.continuousAt.tendsto
  refine ⟨S,B,β,Γ,U,W,hS,hB,hSr,hBr,hvar,hβ,hβ0,hfac,hΓ,hU,hW,hU0,hW0,hUd,hWd,?_,
    ρ,C,hρ,hC,hclose⟩
  filter_upwards[hconj,ht.eventually hfac] with z hz hφ
  exact ⟨hz.1,hz.2.1,hφ.trans hz.2.2⟩
end WP.Analysis

namespace WP.Analysis
def extractionStationaryPhase (S:ℂ→ℂ) (x:ℝ) (u:ℂ):ℂ:=
  centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ)) u

def extractionPremorseGermAmplitude (B:ℂ→ℂ) (Γ:ℕ→ℂ→ℂ) (x:ℝ) (s:ℕ) (u:ℂ):ℂ:=
  Complex.exp (B ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*u))-B (x:ℂ))*
    Γ s ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*u))

def extractionMorseGermAmplitude (B:ℂ→ℂ) (Γ:ℕ→ℂ→ℂ) (x:ℝ) (U:ℂ→ℂ) (s:ℕ) (w:ℂ):ℂ:=
  extractionPremorseGermAmplitude B Γ x s (U w)*deriv U w

lemma actual_extraction_finite_morse_integral_comparison (P:PsiTheory) (p:ℕ) (hp:1≤p) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) (N:ℕ) :
    ∃(S B β:ℂ→ℂ)(Γ:ℕ→ℂ→ℂ)(U W:ℂ→ℂ),
      AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ B (x:ℂ) ∧
      ((fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ))) ∧
      ((fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ))) ∧
      0<WP.euler WP.Psi x ∧ AnalyticAt ℂ β 0 ∧ β 0=0 ∧
      (extractionStationaryPhase S x=ᶠ[𝓝 0] (fun u:ℂ=>u^2*(β u-(1/2:ℂ)))) ∧
      (∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
        (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
          (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ))) ∧
      AnalyticAt ℂ U 0 ∧ U 0=0 ∧ deriv U 0=1 ∧
      (∀s,AnalyticAt ℂ (extractionMorseGermAmplitude B Γ x U s) 0) ∧
      ∃r0:ℝ,0<r0 ∧ ∀r∈Ioc (0:ℝ) r0,∃D ε:ℝ,0<D ∧ 0<ε ∧ ∀h:ℝ,1≤h→
        ‖(∑s∈Finset.range (N+1),(∫u:ℝ in (-r)..r,Complex.exp ((h:ℂ)*extractionStationaryPhase S x (u:ℂ))*
            extractionPremorseGermAmplitude B Γ x s (u:ℂ))/(h:ℂ)^s)-
          (∑s∈Finset.range (N+1),(∫w:ℝ in (-r)..r,Complex.exp (-(h:ℂ)/2*(w:ℂ)^2)*
            extractionMorseGermAmplitude B Γ x U s (w:ℂ))/(h:ℂ)^s)‖≤D*Real.exp (-(ε*h)) := by
  obtain ⟨S,B,β,Γ,U,W,hS,hB,hSr,hBr,hvar,hβ,hβ0,hfac,hΓ,hU,hW,hU0,hW0,hUd,hWd,hconj,
    ρ,C,hρ,hC,hclose⟩:=actual_extraction_stationary_morse_germs P p hp x hx
  let c:ℂ:=Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ)
  have harg:AnalyticAt ℂ (fun u:ℂ=>(x:ℂ)*Complex.exp (c*u)) 0:=by fun_prop
  have harg0:(x:ℂ)*Complex.exp (c*0)=(x:ℂ):=by simp
  have hφ:AnalyticAt ℂ (extractionStationaryPhase S x) 0 :=
    (((hS.comp_of_eq harg harg0).sub analyticAt_const).sub (by fun_prop))
  have ha(s:ℕ):AnalyticAt ℂ (extractionPremorseGermAmplitude B Γ x s) 0 :=
    ((hB.comp_of_eq harg harg0).sub analyticAt_const).cexp.mul ((hΓ s).1.comp_of_eq harg harg0)
  have hpost(s:ℕ):AnalyticAt ℂ (extractionMorseGermAmplitude B Γ x U s) 0:=
    ((ha s).comp_of_eq hU hU0).mul hU.deriv
  have hconj':∀ᶠz:ℂ in 𝓝 0,U (W z)=z ∧ extractionStationaryPhase S x (U z)=-z^2/2 := by
    filter_upwards[hconj] with z hz
    exact ⟨hz.1,hz.2.2⟩
  obtain ⟨r0,hr0,herror⟩:=fixed_morse_finite_amplitude_integral_comparison
    (extractionStationaryPhase S x) U W (extractionPremorseGermAmplitude B Γ x) N hφ hU hW hU0
    (fun s hs=>ha s) hconj' ρ C hρ hC (fun z hz=>(hclose z hz).2)
  exact ⟨S,B,β,Γ,U,W,hS,hB,hSr,hBr,hvar,hβ,hβ0,hfac,hΓ,hU,hU0,hUd,hpost,r0,hr0,herror⟩
end WP.Analysis
