import WPFormalization.Volumes.CompactFiniteModelGrowth
/-! Actual compact phase and amplitude data for a previously fixed canonical
family. The coefficient functions and the Gevrey rate B are unchanged. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma actual_compact_model_uniform_data_of_fixed_coefficients (P:PsiTheory)(p:ℕ)
    (a b:ℝ)(ha:0<a)(hab:a≤b)(hbc:b<xCritical)
    (Ωf:Set ℂ)(f:ℕ→ℂ→ℂ)(C₀ B:ℝ)(hΩf:IsOpen Ωf)
    (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ωf)(hC₀:0<C₀)(hB:0<B)
    (hFa:∀j,AnalyticOnNhd ℂ (f j) Ωf)
    (hfr:∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hfb:∀j z,z∈Ωf→‖f j z‖≤C₀*B^j*(j.factorial:ℝ)^2):
    ∃(S l Bc:ℂ→ℂ)(Ω:Set ℂ)(r C:ℝ),IsOpen Ω ∧
      (∀x∈Icc a b,(x:ℂ)∈Ω) ∧ 0<r ∧ 0<C ∧
      (∀x∈Icc a b,AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ l (x:ℂ) ∧
        (∀ᶠt:ℝ in 𝓝 x,S (t:ℂ)=(extractionS t:ℂ)) ∧
        complexEuler S (x:ℂ)=(WP.Psi x:ℂ) ∧
        ((complexEuler^[2]) S) (x:ℂ)=(WP.euler WP.Psi x:ℂ) ∧
        l (x:ℂ)=((Real.sqrt (WP.euler WP.Psi x))⁻¹:ℝ) ∧
        ∀ᶠq:ℂ in 𝓝 (x:ℂ),(l q)^2*((complexEuler^[2]) S) q=1) ∧
      (∀x∈Ico (0:ℝ) xCritical,AnalyticAt ℂ Bc (x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      (∀j,AnalyticOnNhd ℂ (compactPremorseAmplitude P Bc l f j) (Ω ×ˢ Metric.ball 0 r)) ∧
      ∀x∈Ω,∀u:ℂ,‖u‖<r→AnalyticAt ℂ (centeredExponentialPhase S l) (x,u) ∧
        ‖centeredExponentialPhase S l (x,u)‖≤‖u‖^2 ∧
        ‖compactModelPoint l (x,u)‖<xCritical ∧
        ∀j,‖compactPremorseAmplitude P Bc l f j (x,u)‖≤C*B^j*(j.factorial:ℝ)^2:=by
  obtain ⟨S,l,U,rU,hU,hcoverU,hposU,hData,hPhase⟩:=actual_compact_phase_uniform_bound a b ha hab hbc
  obtain ⟨Bc,hBc0,hBc⟩:=extractionB_complex_extension P p
  obtain ⟨V,rV,C,hV,hcoverV,hrV,hC,hAf,hAb⟩:=
    compact_premorse_family_of_fixed_coefficients P p a b ha hab hbc l Bc
      (fun x hx=>(hData x hx).2.1) hBc Ωf f C₀ B hΩf hcover hC₀ hB hFa hfr hfb
  refine ⟨S,l,Bc,U∩V,min rU rV,C,hU.inter hV,
    (fun x hx=>⟨hcoverU x hx,hcoverV x hx⟩),lt_min hposU hrV,hC,hData,hBc,?_,?_⟩
  · intro j z hz
    apply hAf j z
    refine ⟨hz.1.2,?_⟩
    rw[Metric.mem_ball,dist_zero_right]
    have hz2:‖z.2‖< min rU rV:=by simpa only[Metric.mem_ball,dist_zero_right] using hz.2
    exact hz2.trans_le (min_le_right _ _)
  · intro x hx u hu
    have h1:=hPhase x hx.1 u (hu.trans_le (min_le_left _ _))
    have h2:=hAb x hx.2 u (hu.trans_le (min_le_right _ _))
    exact ⟨h1.1,h1.2,h2.1,h2.2⟩
end WP.Analysis
