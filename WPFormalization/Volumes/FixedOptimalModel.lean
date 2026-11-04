import WPFormalization.Analysis.SmallDiskComparison
import WPFormalization.Volumes.OriginFiniteModel
import WPFormalization.HigherOrder.OptimalMarkedBudget
/-! A single actual optimal-model choice for both finite-model coefficient
calculus and true-generating-function comparison. The native Gevrey budget,
common coefficient family, whole-interval real relative error and actual
origin small-disk comparison are retained together. Generic helpers consume
fixed proved parameter data; the final P-only producer supplies those data. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma origin_normalized_model_data_of_fixed_optimal_parameters
    (P:PsiTheory) (p:ℕ) (hp:1≤p)
    (Ω:Set ℂ) (L:ℕ→ℂ→ℂ) (C B κ a H₀:ℝ)
    (hΩ:IsOpen Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C) (hB:0<B) (hκ:0<κ) (ha:0<a) (hH₀:0<H₀)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hL0:∀z,L 0 z=1)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2)
    (hmodel: ∀g:ℕ,H₀≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        (∀z∈Ω,‖finiteMarkedFactor L h J z-1‖≤2*C*B/h ∧
          1/2≤‖finiteMarkedFactor L h J z‖ ∧
          ‖finiteMarkedFactor L h J z‖≤2 ∧ finiteMarkedFactor L h J z≠0) ∧
        (∀Y∈Icc (0:ℝ) y₀,
          finiteMarkedFactor L h J (Y:ℂ)=(realFiniteMarkedFactor P p h J Y:ℂ)) ∧
        (∀Y∈Ico (0:ℝ) y₀,
          |(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
            realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h))):
    ∃(S Bc:ℂ→ℂ)(H ρ D E:ℝ),
      H₀≤H ∧ 0<H ∧ 0<ρ ∧ ρ<xCritical ∧ 0<D ∧ 0<E ∧
      S 0=0 ∧ Bc 0=1 ∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ)) ∧
      (∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        (∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z ∧
          ‖normalizedFiniteMarkedModel P g p S Bc L J z‖≤D*Real.exp (D*h*‖z‖)) ∧
        (∀x∈Icc (0:ℝ) ρ,normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)≠0 ∧
          ‖normalizedMarkedGenerating P g p (x:ℂ)/normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)-1‖≤
            E*Real.exp (-a*Real.sqrt h)):=by
  obtain ⟨Bc,ρ₀,D₀,hρ₀,hρ₀x,hD₀,hBc0,hBcp,hlocal,hampA,hampB,hampR⟩:=
    origin_marked_amplitude_family_of_parameter_data P p Ω L C B hΩ hcover hC hB hLa hLr hLb
  obtain ⟨S,hSa,hS0,hSd,hSreal⟩:=Analysis.exists_extractionS_origin_complex_extension
  obtain ⟨rs,Cs,hrs,hCs,hSbound⟩:=Analysis.complex_analytic_zero_linear_bound S hSa hS0
  obtain ⟨rreal,hrreal,hSrealball⟩:=Metric.eventually_nhds_iff.mp hSreal
  let ρ:ℝ:=min ρ₀ (min rs (rreal/2))
  let D:ℝ:=Cs+4
  let H:ℝ:=max H₀ 1
  have hρ:0<ρ:=lt_min hρ₀ (lt_min hrs (by positivity))
  have hρle:ρ≤ρ₀:=min_le_left _ _
  have hρs:ρ≤rs:=(min_le_right _ _).trans (min_le_left _ _)
  have hρr:ρ<rreal:=lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  have hρx:ρ<xCritical:=hρle.trans_lt hρ₀x
  have hD:0<D:=by dsimp[D];linarith
  have hH:0<H:=hH₀.trans_le (le_max_left _ _)
  have hSphys:∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ):=by
    intro x hx
    exact hSrealball (show dist x 0<rreal by rw[Real.dist_eq,sub_zero,abs_of_nonneg hx.1];exact hx.2.trans_lt hρr) hx.1
  refine ⟨S,Bc,H,ρ,D,2*C,le_max_left _ _,hH,hρ,hρx,hD,by positivity,hS0,hBc0,hLr,?_,?_⟩
  · intro x hx
    exact ⟨hSphys x hx,(hBcp x ⟨hx.1,hx.2.trans_lt hρx⟩).2⟩
  · intro g hg
    dsimp only
    let h:ℝ:=complexity g p
    let J:=⌊κ*Real.sqrt h⌋₊
    have hh:0<h:=hH.trans_le hg
    have hg₀:H₀≤h:=(le_max_left _ _).trans hg
    have hh1:1≤h:=(le_max_right _ _).trans hg
    have hs:Stable g p:=by
      have hn:1≤complexity g p:=by exact_mod_cast (show (1:ℝ)≤(complexity g p:ℝ) from hh1)
      unfold Stable complexity at *;omega
    have hm:=hmodel g hg₀
    have hPana:=finiteMarkedFactor_analyticOnNhd Ω L h J hLa
    refine ⟨?_,?_⟩
    · intro z hz
      have hl:=hlocal z (hz.trans hρle)
      have hsbound:=hSbound z (hz.trans hρs)
      have hYca:=PositiveConvolution.planarInverse_analyticAt P z (hz.trans_lt hρx)
      have hPbound:‖finiteMarkedFactor L h J (PositiveConvolution.planarInverse P z)‖≤2:=
        (hm.1 _ hl.2.2).2.2.1
      have hAa:AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z:=
        ((analyticAt_const.mul hsbound.1).cexp.mul hl.1).mul ((hPana _ hl.2.2).comp hYca)
      refine ⟨hAa,?_⟩
      have hex:‖Complex.exp ((complexity g p:ℂ)*S z)‖≤Real.exp (D*h*‖z‖):=by
        apply (Complex.norm_exp_le_exp_norm _).trans
        apply Real.exp_le_exp.mpr
        rw[norm_mul,Complex.norm_natCast]
        have ht:=mul_le_mul_of_nonneg_left hsbound.2 (Nat.cast_nonneg (complexity g p): (0:ℝ)≤complexity g p)
        have hd:Cs≤D:=by dsimp[D];linarith
        have ht':Cs*‖z‖≤D*‖z‖:=mul_le_mul_of_nonneg_right hd (norm_nonneg _)
        nlinarith[mul_le_mul_of_nonneg_left ht' hh.le]
      unfold normalizedFiniteMarkedModel
      rw[norm_mul,norm_mul]
      have hprod:=mul_le_mul (mul_le_mul hex hl.2.1 (norm_nonneg _) (Real.exp_pos _).le)
        hPbound (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (by norm_num:(0:ℝ)≤2))
      have hd4:(4:ℝ)≤D:=by dsimp[D];linarith
      have ht:=mul_le_mul_of_nonneg_right hd4 (Real.exp_pos (D*h*‖z‖)).le
      nlinarith
    · intro x hx
      have hxi:x∈Ico (0:ℝ) xCritical:=⟨hx.1,hx.2.trans_lt hρx⟩
      have hy:=(inverseY_branch x hxi).1
      have hyc:inverseY x∈Icc (0:ℝ) y₀:=⟨hy.1,hy.2.le⟩
      have hPL:=hm.2.1 _ hyc
      have hPne:realFiniteMarkedFactor P p h J (inverseY x)≠0:=by
        intro he
        have hnonzero:finiteMarkedFactor L h J (inverseY x:ℂ)≠0:=(hm.1 _ (hcover _ hyc)).2.2.2
        apply hnonzero
        rw[hPL,he,Complex.ofReal_zero]
      have hbval: Bc (x:ℂ)=(extractionB p x:ℂ):=(hBcp x hxi).2
      have hmreal:=normalizedFiniteMarkedModel_real P g p hs S Bc L J x hxi (hSphys x hx) hbval hPL
      have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
      have hMY:markedModel g p (inverseY x)≠0:=(markedModel_pos_parameter g p hs _ hy).ne'
      refine ⟨?_,?_⟩
      · rw[hmreal]
        exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (div_ne_zero hMY hM0) hPne)
      · rw[normalized_model_real_relative_error_identity P g p hs S Bc L J x hxi (hSphys x hx) hbval hPL hPne]
        have ht:=hm.2.2 (inverseY x) hy
        simpa only[(inverseY_branch x hxi).2] using ht
end WP.HigherOrder

namespace WP.HigherOrder
open Set
lemma origin_small_disk_comparison_of_fixed_model
    (P:PsiTheory) (p:ℕ) (hp:1≤p)
    (Ω:Set ℂ) (L:ℕ→ℂ→ℂ) (C B κ a H₀:ℝ)
    (hΩ:IsOpen Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C) (hB:0<B) (hκ:0<κ) (ha:0<a) (hH₀:0<H₀)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hL0:∀z,L 0 z=1)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2)
    (hmodel: ∀g:ℕ,H₀≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        (∀z∈Ω,‖finiteMarkedFactor L h J z-1‖≤2*C*B/h ∧
          1/2≤‖finiteMarkedFactor L h J z‖ ∧
          ‖finiteMarkedFactor L h J z‖≤2 ∧ finiteMarkedFactor L h J z≠0) ∧
        (∀Y∈Icc (0:ℝ) y₀,
          finiteMarkedFactor L h J (Y:ℂ)=(realFiniteMarkedFactor P p h J Y:ℂ)) ∧
        (∀Y∈Ico (0:ℝ) y₀,
          |(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
            realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h))):
    ∃(S Bc:ℂ→ℂ)(d Cs H ρ:ℝ),H₀≤H ∧
      0<d ∧ 0<Cs ∧ 0<H ∧ 0<ρ ∧ ρ<xCritical ∧ S 0=0 ∧ Bc 0=1 ∧
      (∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→∀z:ℂ,‖z‖≤d/(4*Real.sqrt (complexity g p))→
        ‖normalizedMarkedGenerating P g p z-
          normalizedFiniteMarkedModel P g p S Bc L ⌊κ*Real.sqrt (complexity g p)⌋₊ z‖≤
            Cs*Real.exp (-(a/4)*Real.sqrt (complexity g p)):=by
  obtain ⟨S,Bc,H₁,ρ,D,E,hH₀₁,hH₁,hρ,hρx,hD,hE,hS0,hBc0,hLr',hSR,hdata⟩:=
    origin_normalized_model_data_of_fixed_optimal_parameters P p hp Ω L C B κ a H₀
      hΩ hcover hC hB hκ ha hH₀ hLa hL0 hLr hLb hmodel
  let d:ℝ:=min (ρ/18) (a/(36*D))
  let H:ℝ:=max H₁ 1
  have hd:0<d:=lt_min (by positivity) (by positivity)
  have hdr:d≤ρ/18:=min_le_left _ _
  have hda:36*D*d≤a:=by
    have ht:=(le_div_iff₀ (by positivity:0<36*D)).mp (min_le_right (ρ/18) (a/(36*D)))
    dsimp only[d]
    nlinarith
  have hH:0<H:=hH₁.trans_le (le_max_left _ _)
  refine ⟨S,Bc,d,(E+2)*D,H,ρ,hH₀₁.trans (le_max_left _ _),hd,by positivity,hH,hρ,hρx,hS0,hBc0,hSR,?_⟩
  intro g hg z hz
  let h:ℝ:=complexity g p
  let J:=⌊κ*Real.sqrt h⌋₊
  have hh1:1≤h:=(le_max_right _ _).trans hg
  have hg₁:H₁≤h:=(le_max_left _ _).trans hg
  have hs:Stable g p:=by
    have hn:1≤complexity g p:=by exact_mod_cast (show (1:ℝ)≤(complexity g p:ℝ) from hh1)
    unfold Stable complexity at *;omega
  have hm:=hdata g hg₁
  have hM:AnalyticOnNhd ℂ (normalizedFiniteMarkedModel P g p S Bc L J) (Metric.ball 0 ρ):=by
    intro w hw
    exact (hm.1 w (show ‖w‖≤ρ from (by simpa only[Metric.mem_ball,dist_zero_right] using hw : ‖w‖<ρ).le)).1
  exact Analysis.small_disk_comparison_of_real_relative_error
    (normalizedMarkedGenerating P g p) (normalizedFiniteMarkedModel P g p S Bc L J)
    ρ D E a d h hρ hD hE ha hd hdr hda hh1
    (normalizedMarkedGenerating_analytic_disk P g p ρ hρx.le) hM
    (fun w hw=>(hm.1 w hw).2)
    (fun w hw=>normalizedMarkedGenerating_disk_domination P g p hp hs ‖w‖ ⟨norm_nonneg _,hw.trans_lt hρx⟩ w le_rfl)
    hm.2 z hz
end WP.HigherOrder

namespace WP.HigherOrder
open Set
lemma actual_optimal_model_comparison_data (P:PsiTheory) (p:ℕ) (hp:1≤p):
    ∃(Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B κ a H:ℝ)(S Bc:ℂ→ℂ)(d Cs ρ:ℝ),
      IsOpen Ω ∧ (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      0<C ∧ 0<B ∧ 0<κ ∧ 0<a ∧ 0<H ∧ 0<d ∧ 0<Cs ∧ 0<ρ ∧ ρ<xCritical ∧
      (∀j,AnalyticOnNhd ℂ (L j) Ω) ∧ (∀z,L 0 z=1) ∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ)) ∧
      (∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2) ∧
      S 0=0 ∧ Bc 0=1 ∧
      (∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        2*B*((J:ℝ)+1)^2≤h ∧
        (∀z∈Ω,‖finiteMarkedFactor L h J z-1‖≤2*C*B/h ∧
          1/2≤‖finiteMarkedFactor L h J z‖ ∧
          ‖finiteMarkedFactor L h J z‖≤2 ∧ finiteMarkedFactor L h J z≠0) ∧
        (∀Y∈Ico (0:ℝ) y₀,|(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
          realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h)) ∧
        (∀z:ℂ,‖z‖≤d/(4*Real.sqrt h)→
          ‖normalizedMarkedGenerating P g p z-normalizedFiniteMarkedModel P g p S Bc L J z‖≤
            Cs*Real.exp (-(a/4)*Real.sqrt h)):=by
  obtain ⟨Ω,L,C,B,κ,a,H₀,hΩ,hcover,hC,hB,hκ,ha,hH₀,hLa,hL0,hLr,hLb,hmodels⟩:=
    optimal_marked_model_real_comparison_with_budget P p hp
  have hmodel:∀g:ℕ,H₀≤(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      (∀z∈Ω,‖finiteMarkedFactor L h J z-1‖≤2*C*B/h ∧
        1/2≤‖finiteMarkedFactor L h J z‖ ∧ ‖finiteMarkedFactor L h J z‖≤2 ∧
        finiteMarkedFactor L h J z≠0) ∧
      (∀Y∈Icc (0:ℝ) y₀,finiteMarkedFactor L h J (Y:ℂ)=(realFiniteMarkedFactor P p h J Y:ℂ)) ∧
      (∀Y∈Ico (0:ℝ) y₀,|(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
        realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h)):=by
    intro g hg
    exact (hmodels g hg).2
  obtain ⟨S,Bc,d,Cs,H,ρ,hH₀H,hd,hCs,hH,hρ,hρx,hS0,hBc0,htrace,hsmall⟩:=
    origin_small_disk_comparison_of_fixed_model P p hp Ω L C B κ a H₀
      hΩ hcover hC hB hκ ha hH₀ hLa hL0 hLr hLb hmodel
  refine ⟨Ω,L,C,B,κ,a,H,S,Bc,d,Cs,ρ,hΩ,hcover,hC,hB,hκ,ha,hH,hd,hCs,hρ,hρx,
    hLa,hL0,hLr,hLb,hS0,hBc0,htrace,?_⟩
  intro g hg
  have hg₀:H₀≤(complexity g p:ℝ):=hH₀H.trans hg
  exact ⟨(hmodels g hg₀).1,(hmodel g hg₀).1,(hmodel g hg₀).2.2,hsmall g hg⟩
end WP.HigherOrder
