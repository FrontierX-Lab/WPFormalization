import WPFormalization.HigherOrder.OriginModelGermMatching
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma origin_poisson_normalized_model_data_for_fixed_source (P:PsiTheory) (p:ℕ)
    (Ω:Set ℂ) (L:ℕ→ℂ→ℂ) (C B:ℝ)
    (hΩ:IsOpen Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C) (hB:0<B) (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω) (hL0:∀z,L 0 z=1)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2)
    (S₀ Bc₀:ℂ→ℂ) (hS₀:AnalyticAt ℂ S₀ 0) (hBc₀:AnalyticAt ℂ Bc₀ 0)
    (hS₀r:∀ᶠt:ℝ in 𝓝 0,0≤t→S₀ (t:ℂ)=(extractionS t:ℂ))
    (hBc₀r:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc₀ (t:ℂ)=(extractionB p t:ℂ)):
    ∃(S Bc:ℂ→ℂ)(Z:ℂ × ℂ → ℂ)(ν₀ E D δ:ℝ),
      0<ν₀∧0<E∧0<D∧0<δ∧AnalyticAt ℂ S 0∧S 0=0∧deriv S 0=2∧
      (∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ))∧
      (∀z:ℂ,‖z‖<δ→S z=S₀ z∧Bc z=Bc₀ z)∧
      (∀n,AnalyticOnNhd ℂ (normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n)
        (Metric.ball 0 ν₀)∧∀ν:ℂ,‖ν‖<ν₀→
        ‖normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n ν‖≤E*D^n*(n.factorial:ℝ)^2)∧
      (∀n,normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n 0=
        (markedCoefficient P p n 0:ℂ))∧
      ∀g k K J:ℕ,0<(complexity g p:ℝ)→(k:ℝ)/(complexity g p:ℝ)≤ν₀→
        (K:ℝ)≤(complexity g p:ℝ)/2→K≤J→2*B*((J:ℝ)+1)^2≤(complexity g p:ℝ)→
          ‖WP.coeff (normalizedFiniteMarkedModel P g p S₀ Bc₀ L J) k /
            ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)-
            ∑n∈Finset.range (K+1),((complexity g p:ℝ):ℂ)⁻¹^n*
              normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n
                ((((k:ℝ)/(complexity g p:ℝ)):ℝ):ℂ)‖≤
            E*D^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1):=by
  obtain ⟨S,Bc,Z,R,ν₀,ρ,A,E,D,hR,hν₀,hν₀R,hρ,hA,hE,hD,hS,hS0,hSd,hBc0,hSr,
    hHa,hHr,hfa,hfb,hcoef,hzero,hfinal⟩:=
      actual_origin_poisson_normalized_model_data_of_parameter_data P p Ω L C B hΩ hcover hC hB hLa hLr hLb
  have hBc:AnalyticAt ℂ Bc 0:=origin_marked_Bc_analyticAt_zero P p Bc L hL0 (hHa 0)
  have hBcr:=origin_marked_Bc_real_germ P p Bc L ρ hρ hL0 (hHr 0)
  obtain ⟨δ,hδ,he⟩:=normalizedFiniteMarkedModel_common_germ_of_real_trace P p S S₀ Bc Bc₀ L
    hS hS₀ hBc hBc₀ hSr hS₀r hBcr hBc₀r
  have hc:=normalizedFiniteMarkedModel_coeff_eq_of_common_germ P p S S₀ Bc Bc₀ L δ hδ (fun z hz=>(he z hz).2.2)
  refine ⟨S,Bc,Z,ν₀,E,D,δ,hν₀,hE,hD,hδ,hS,hS0,hSd,hSr,(fun z hz=>⟨(he z hz).1,(he z hz).2.1⟩),hcoef,hzero,?_⟩
  intro g k K J hh hν hK hKJ hw
  rw[←hc g J k]
  exact (hfinal g k J hh hν).2 K hK hKJ hw
end WP.HigherOrder
