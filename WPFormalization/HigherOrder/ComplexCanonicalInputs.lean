import WPFormalization.HigherOrder.ComplexTriangular
/-! A single genuine parameter domain for the canonical hierarchy's inputs.
The domain is independent of P, genus, marking count and expansion order.
It combines the actual geometric kernel bounds, finite-component Gamma bound,
all moments, and a uniformly invertible actual A. This is input data, not an
all-order estimate or a holomorphy assertion for the canonical hierarchy. -/
set_option maxHeartbeats 800000
noncomputable section
open Set
namespace WP.HigherOrder.ComplexCanonical
open WP.Analysis

lemma common_complex_canonical_inputs :
    ∃ (Ω : Set ℂ) (R : ℂ → ℂ) (ρ C M : ℝ),
      IsOpen Ω ∧ Convex ℝ Ω ∧ (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      1<ρ ∧ 0<C ∧ 0<M ∧ AnalyticOnNhd ℂ R Ω ∧
      (∀ z∈Ω,complexAUnit z≠0 ∧ complexDeflatedCoeff R 0 z≠0) ∧
      (∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 ∧
      AnalyticOnNhd ℂ (kernelA R) Ω ∧
      (∀ z∈Ω,kernelA R z≠0 ∧ ‖kernelA R z‖≤M ∧ ‖(kernelA R z)⁻¹‖≤M) ∧
      (∀ n : ℕ,AnalyticOnNhd ℂ (complexThetaCoeff R n) Ω ∧
        AnalyticOnNhd ℂ (complexWeightCoeff R n) Ω ∧
        AnalyticOnNhd ℂ (complexDilatonCoefficient R n) Ω ∧
        AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω ∧
        AnalyticOnNhd ℂ (regularizedKernelCoeff H R n) Ω) ∧
      (∀ z∈Ω,∀ n : ℕ,‖complexThetaCoeff R n z‖≤C ∧
        ‖complexWeightCoeff R n z‖≤C/ρ^n ∧ ‖complexDilatonCoefficient R n z‖≤C/ρ^n) ∧
      (∀ n : ℕ,complexThetaCoeff R n (y₀:ℂ)=1) ∧
      (∀ j : ℕ,AnalyticOnNhd ℂ (complexKernelMoment R j) Ω ∧
        AnalyticOnNhd ℂ (complexBMoment R j) Ω ∧
        ∀ Y∈Icc (0:ℝ) y₀,complexKernelMoment R j (Y:ℂ)=(WP.HigherOrder.kernelMoment j Y:ℂ) ∧
          complexBMoment R j (Y:ℂ)=(WP.HigherOrder.bMoment j Y:ℂ)) ∧
      (∀ (P : PsiTheory) (g : ℕ) (d : List ℕ),AnalyticOnNhd ℂ (complexSmallW P R g d) Ω ∧
        ∀ Y∈Icc (0:ℝ) y₀,complexSmallW P R g d (Y:ℂ)=(WP.HigherOrder.smallW P Y g d:ℂ)) ∧
      (∀ P : PsiTheory,∃ T : ℝ,1≤T ∧ ∀ g : ℕ,∀ d : List ℕ,Stable g d.length → ∀ z∈Ω,
        ‖complexSmallW P R g d z‖≤Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length)) ∧
      (∀ (P : PsiTheory) (Y : ℝ),Y∈Icc (0:ℝ) y₀ → ∀ k : ℕ,
        (∀ d,profileCoefficient P R (Y:ℂ) d k=(WP.HigherOrder.profileCoefficient P Y d k:ℂ)) ∧
        (∀ p,cuspCoefficient P R (Y:ℂ) p k=(WP.HigherOrder.cuspCoefficient P Y p k:ℂ)) ∧
        (∀ p,genusCoefficient P R (Y:ℂ) p k=(WP.HigherOrder.genusCoefficient P Y p k:ℂ))) := by
  obtain ⟨U,R,ρ,C,hU,hUv,hcoverU,hρ,hC,hR,hunit,hraw,hR0,hR',hcoef,hmatch,hbound,hcrit,hsmall,hgrowth⟩ :=
    common_complex_small_component_bounds
  obtain ⟨Ω,M,hΩ,hΩv,hcover,hΩU,hM,hA,hAb⟩ :=
    exists_convex_kernelA_uniform_control U hU hcoverU R hR hR0 hraw (fun z hz=>(hunit z hz).1)
  have hRΩ : AnalyticOnNhd ℂ R Ω := hR.mono hΩU
  have hunitΩ : ∀ z∈Ω,complexAUnit z≠0 := fun z hz=>(hunit z (hΩU hz)).1
  have hc := normalized_coefficients_holomorphic_on_common_domain Ω hΩ hcover R hRΩ hR0 hraw hunitΩ
  have hj := normalized_kernel_jets_holomorphic_on_common_domain Ω hΩ hcover R hRΩ hR0 hraw hunitΩ
  have hD : ∀ n : ℕ,AnalyticOnNhd ℂ (complexDeflatedCoeff R n) Ω :=
    complexDeflatedCoeff_analyticOnNhd Ω R (fun j=>(hj j 1).1)
  have hW : ∀ n : ℕ,AnalyticOnNhd ℂ (complexWeightShiftCoeff R n) Ω :=
    complexWeightShiftCoeff_analyticOnNhd Ω R hD (fun z hz=>(hunit z (hΩU hz)).2)
  refine ⟨Ω,R,ρ,C,M,hΩ,hΩv,hcover,hρ,hC,hM,hRΩ,
    (fun z hz=>hunit z (hΩU hz)),hraw,hR0,hR',hA,
    (fun z hz=>hAb z (subset_closure hz)),?_,?_,hcrit,?_,?_,?_,?_⟩
  · intro n
    exact ⟨(hcoef n).1.mono hΩU,(hcoef n).2.1.mono hΩU,
      (hcoef n).2.2.mono hΩU,(hc n).1,(hc n).2.1⟩
  · intro z hz n
    exact hbound z (hΩU hz) n
  · intro j
    refine ⟨complexKernelMoment_analyticOnNhd Ω R hW j,
      complexBMoment_analyticOnNhd Ω R (fun k=>(hj k 1).2.1) j,?_⟩
    intro Y hY
    exact ⟨complexKernelMoment_restrict_closed R (fun k Y hY=>((hj k 1).2.2 Y hY).1) j Y hY,
      complexBMoment_restrict_closed R (fun k Y hY=>((hj k 1).2.2 Y hY).2) j Y hY⟩
  · intro P g d
    exact ⟨(hsmall P g d).1.mono hΩU,(hsmall P g d).2⟩
  · intro P
    obtain ⟨T,hT,hg⟩ := hgrowth P
    exact ⟨T,hT,fun g d hs z hz=>hg g d hs z (hΩU hz)⟩
  · intro P Y hY k
    exact canonical_coefficients_restrict_closed Ω hΩ hcover R hRΩ hR0 hraw hunitΩ P Y hY k

end WP.HigherOrder.ComplexCanonical
