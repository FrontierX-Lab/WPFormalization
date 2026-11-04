import WPFormalization.HigherOrder.MatchedOriginPoissonData
/-! The true origin finite-model coefficient expansion uses the original
canonical CG3 coefficients, including the prescribed zero-density endpoint. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma actual_origin_canonical_model_expansion_of_parameter_data (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B:ℝ)
    (hΩ:IsOpen Ω)(hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C)(hB:0<B)(hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)(hL0:∀z,L 0 z=1)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃(S Bc:ℂ→ℂ)(δ E D:ℝ),0<δ ∧ 0<E ∧ 0<D ∧
      AnalyticAt ℂ S 0 ∧ AnalyticAt ℂ Bc 0 ∧ S 0=0 ∧ Bc 0=1 ∧
      (∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ)) ∧
      (∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ)) ∧
      ∀g k K J:ℕ,0<(complexity g p:ℝ)→(k:ℝ)/(complexity g p:ℝ)≤δ→
        (K:ℝ)≤(complexity g p:ℝ)/2→K≤J→2*B*((J:ℝ)+1)^2≤(complexity g p:ℝ)→
        ‖WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k /
          ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)-
          ∑n∈Finset.range (K+1),((complexity g p:ℝ):ℂ)⁻¹^n*
            (extractedCoefficient P p n (densityY (2*(k:ℝ)/(complexity g p:ℝ))):ℂ)‖≤
          E*D^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1):=by
  obtain ⟨S,Bc,Z,δ,E,D,hδ,hE,hD,hS,hS0,hSd,hBc0,hBc,hSr,hBr,hcoef,hzero,hraw,herror⟩:=
    actual_matched_origin_poisson_data_of_parameter_data P p hp Ω L C B hΩ hcover hC hB hLa hL0 hLr hLb
  refine ⟨S,Bc,δ/2,E,D,half_pos hδ,hE,hD,hS,hBc,hS0,hBc0,hSr,hBr,?_⟩
  intro g k K J hh hν hK hKJ hbudget
  let ν:ℝ:=(k:ℝ)/(complexity g p:ℝ)
  have hν0:0≤ν:=by dsimp[ν];positivity
  have hνδ:ν<δ:=hν.trans_lt (half_lt_self hδ)
  have hdy:∀n,normalizedPoissonFamilyCoefficient (fun s=>originPoissonAmplitude P p s Bc L Z) n (ν:ℂ)=
      (extractedCoefficient P p n (densityY (2*ν)):ℂ):=by
    intro n
    by_cases hv:ν=0
    · have hy0:densityY 0=0:=by
        have hs:=WP.Analysis.densityY_spec 0 le_rfl
        exact WP.Analysis.density_strictMonoOn.injOn hs.1 ⟨le_rfl,y₀_pos⟩ (hs.2.trans density_zero_value.symm)
      simp only[hv,mul_zero,Complex.ofReal_zero,hy0,extractedCoefficient_at_zero]
      exact hzero n
    · have hνp:0<ν:=lt_of_le_of_ne hν0 (Ne.symm hv)
      have hs:=WP.Analysis.densityY_spec (2*ν) (by positivity)
      have hY0:densityY (2*ν)≠0:=by
        intro h
        rw[h,density_zero_value] at hs
        linarith[hs.2]
      rw[hraw ν ⟨hνp,hνδ⟩ n,extractedCoefficient,if_neg hY0,if_neg (ne_of_lt hs.1.2)]
  dsimp only[ν] at hdy
  have he:=herror g k K J hh hνδ.le hK hKJ hbudget
  simp_rw[hdy] at he
  simpa only[mul_div_assoc] using he
end WP.HigherOrder
