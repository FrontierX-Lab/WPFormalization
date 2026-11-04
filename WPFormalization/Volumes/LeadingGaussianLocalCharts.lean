import WPFormalization.Volumes.LeadingGaussianChart
import WPFormalization.Volumes.OriginStandardPhysical
import WPFormalization.Volumes.CompactLeadingChart
import WPFormalization.Volumes.CriticalVarianceLower
import WPFormalization.Analysis.VarianceCompactLower
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
namespace WP
open Set Filter Complex
open scoped Topology
set_option autoImplicit false

lemma actual_origin_leading_charts (P:PsiTheory)(p:ℕ):
    ∃η ρ C D K:ℝ,0<η ∧ η<xCritical ∧ 0<ρ ∧ 0<C ∧ 0<D ∧ 0<K ∧
      (∀x∈Ioo (0:ℝ) η,1≤deriv Psi x ∧ Psi x≤K*x) ∧
      ∀x∈Ioo (0:ℝ) η,∀g:ℕ,Stable g p→0<(complexity g p:ℝ)→
        LeadingGaussianChart g p x (ρ*Real.sqrt ((complexity g p:ℝ)*x)) C D:=by
  obtain ⟨S,hS,_,hSd,hSr⟩:=Analysis.exists_extractionS_origin_complex_extension
  obtain ⟨Bc,hBc0,hBphys⟩:=Analysis.extractionB_complex_extension P p
  have hzero:(0:ℝ)∈Ico (0:ℝ) xCritical:=⟨le_rfl,Analysis.xCritical_pos_parameter⟩
  have hBc:AnalyticAt ℂ Bc 0:=by simpa only[Complex.ofReal_zero] using (hBphys 0 hzero).1
  have hBr:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ):=by
    filter_upwards[eventually_lt_nhds Analysis.xCritical_pos_parameter] with t ht ht0
    exact (hBphys t ⟨ht0,ht⟩).2
  obtain ⟨G,Amp,η,ρ,C,D,K,hη,hηx,hρ,hC,hD,hK,hmean,hstd,htrace⟩:=
    Analysis.origin_standard_gaussian_physical_data p S Bc hS hSd hBc
      (by rw[hBc0];exact one_ne_zero) hSr hBr
  refine ⟨η,ρ,C,D,K,hη,hηx,hρ,hC,hD,hK,hmean,?_⟩
  intro x hx g hs hh
  let h:ℝ:=complexity g p
  obtain ⟨hLa,hAa,hL0,hL1,hL2,hA0,hbound⟩:=hstd h x hh hx
  refine ⟨Analysis.originStandardLog G h x,Analysis.originStandardAmplitude Amp h x,
    hLa,?_,hL1,hL2,?_,hAa,hA0,?_,?_⟩
  · simpa only[WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one] using hL0
  · intro w hw
    exact (hbound w hw.le).1
  · intro w hw
    exact (hbound w hw.le).2.1
  · intro u hu
    dsimp only
    have ht:=htrace h x u hh hx hu.le
    have he:=(hbound (u:ℂ) (by simpa only[Complex.norm_real,Real.norm_eq_abs] using hu.le)).2.2
    dsimp only at he ht
    have hz:(x:ℂ)*Complex.exp ((u:ℂ)/(Real.sqrt (h*euler Psi x):ℂ))=
        ((x*Real.exp (u/Real.sqrt (h*euler Psi x)):ℝ):ℂ):=by
      rw[←Complex.ofReal_div,←Complex.ofReal_exp,←Complex.ofReal_mul]
    rw[hz,ht.2.2.2 g hs rfl] at he
    refine ⟨ht.1,?_⟩
    dsimp only[h] at he ⊢
    apply he.symm.trans
    congr 2
    push_cast
    ring

lemma actual_critical_leading_charts (P:PsiTheory)(p:ℕ):
    ∃η ρ C D:ℝ,0<η ∧ η<y₀ ∧ 0<ρ ∧ 0<C ∧ 0<D ∧
      ∀δ∈Ioo (0:ℝ) η,1≤euler Psi (XR (y₀-δ)) ∧
        ∀g:ℕ,Stable g p→0<(complexity g p:ℝ)→
          LeadingGaussianChart g p (XR (y₀-δ)) (ρ*Real.sqrt (complexity g p:ℝ)) C D:=by
  obtain ⟨d,Q,ρ,C,D,_,_,_,hρ,hρy,hC,hD,hdata⟩:=
    Analysis.actual_critical_leading_gaussian_chart P p
  obtain ⟨ηv,hηv,hηvy,hvar⟩:=Analysis.critical_variance_ge_one
  let η:ℝ:=min ρ ηv
  have hη:0<η:=lt_min hρ hηv
  refine ⟨η,ρ,C,D,hη,(min_le_left _ _).trans_lt hρy,hρ,hC,hD,?_⟩
  intro δ hδ
  refine ⟨hvar δ ⟨hδ.1,hδ.2.trans_le (min_le_right _ _)⟩,?_⟩
  intro g hs hh
  let h:ℝ:=complexity g p
  obtain ⟨hLa,hL0,hL1,hL2,hLb,hAa,hA0,hAb,htrace⟩:=
    hdata δ ⟨hδ.1,hδ.2.trans_le (min_le_left _ _)⟩ g hs hh
  refine ⟨d.centeredLogAction h (δ:ℂ),d.leadingCenteredAmplitude Q p h (δ:ℂ),
    hLa,hL0,hL1,hL2,hLb,hAa,hA0,hAb,?_⟩
  intro u hu
  have he:=htrace u hu
  dsimp only at he ⊢
  have hi:inverseY (XR (y₀-δ))=y₀-δ:=Analysis.inverseY_eq_of_root _ _ (by linarith[hδ.1]) rfl
  simpa only[hi] using he

lemma actual_compact_leading_charts (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (a b:ℝ)(ha:0<a)(hab:a≤b)(hb:b<xCritical):
    ∃ρ C D v:ℝ,0<ρ ∧ 0<C ∧ 0<D ∧ 0<v ∧
      ∀x∈Icc a b,v≤euler Psi x ∧ ∀g:ℕ,Stable g p→0<(complexity g p:ℝ)→
        LeadingGaussianChart g p x (ρ*Real.sqrt (complexity g p:ℝ)) C D:=by
  obtain ⟨S,L,Bc,f,ρ,C,D,hρ,hC,hD,hdata⟩:=
    Analysis.actual_compact_leading_gaussian_chart P p hp a b ha hab hb
  obtain ⟨v,hv,hvar⟩:=Analysis.compact_eulerPsi_positive_lower a b ha hab hb
  refine ⟨ρ,C,D,v,hρ,hC,hD,hv,?_⟩
  intro x hx
  refine ⟨hvar x hx,?_⟩
  intro g hs hh
  let h:ℝ:=complexity g p
  obtain ⟨hLa,hL0,hL1,hL2,hLb,hAa,hA0,hAb,htrace⟩:=hdata x hx g hs hh
  exact ⟨Analysis.compactCenteredLogAction S L h (x:ℂ),
    Analysis.compactLeadingCenteredAmplitude P Bc L f h (x:ℂ),
    hLa,hL0,hL1,hL2,hLb,hAa,hA0,hAb,htrace⟩

end WP
