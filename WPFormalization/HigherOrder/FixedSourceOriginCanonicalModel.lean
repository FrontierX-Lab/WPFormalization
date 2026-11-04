import WPFormalization.HigherOrder.OriginCanonicalModel
/-! The origin coefficient expansion transfers to an already chosen actual
phase/amplitude source by equality of all finite-model Taylor coefficients.
The input canonical LC family and its native term budget remain the same. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma fixed_source_origin_canonical_model_expansion (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B:ℝ)
    (hΩ:IsOpen Ω)(hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C)(hB:0<B)(hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)(hL0:∀z,L 0 z=1)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2)
    (S0 Bc0:ℂ→ℂ)(hS0:AnalyticAt ℂ S0 0)(hBc0:AnalyticAt ℂ Bc0 0)
    (hSr0:∀ᶠt:ℝ in 𝓝 0,0≤t→S0 (t:ℂ)=(extractionS t:ℂ))
    (hBr0:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc0 (t:ℂ)=(extractionB p t:ℂ)):
    ∃δ E D:ℝ,0<δ ∧ 0<E ∧ 0<D ∧
      ∀g k K J:ℕ,0<(complexity g p:ℝ)→(k:ℝ)/(complexity g p:ℝ)≤δ→
        (K:ℝ)≤(complexity g p:ℝ)/2→K≤J→2*B*((J:ℝ)+1)^2≤(complexity g p:ℝ)→
        ‖WP.coeff (normalizedFiniteMarkedModel P g p S0 Bc0 L J) k /
          ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)-
          ∑n∈Finset.range (K+1),((complexity g p:ℝ):ℂ)⁻¹^n*
            (extractedCoefficient P p n (densityY (2*(k:ℝ)/(complexity g p:ℝ))):ℂ)‖≤
          E*D^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1):=by
  obtain ⟨S,Bc,δ,E,D,hδ,hE,hD,hS,hBc,hSz,hBcz,hSr,hBr,herror⟩:=
    actual_origin_canonical_model_expansion_of_parameter_data P p hp Ω L C B hΩ hcover hC hB hLa hL0 hLr hLb
  obtain ⟨δg,hδg,he⟩:=normalizedFiniteMarkedModel_common_germ_of_real_trace P p S S0 Bc Bc0 L
    hS hS0 hBc hBc0 hSr hSr0 hBr hBr0
  have hc:=normalizedFiniteMarkedModel_coeff_eq_of_common_germ P p S S0 Bc Bc0 L δg hδg
    (fun z hz=>(he z hz).2.2)
  refine ⟨δ,E,D,hδ,hE,hD,?_⟩
  intro g k K J hh hν hK hKJ hbudget
  rw[←hc g J k]
  exact herror g k K J hh hν hK hKJ hbudget
end WP.HigherOrder
