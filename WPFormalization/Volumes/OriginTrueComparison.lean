import WPFormalization.Volumes.OriginFiniteModelGrowth
import WPFormalization.Volumes.CriticalTrueComparison
/-! The true marked generating function and its same-choice finite origin
model on the growing standardized disk. Actual normalization and the proved
real relative error give the real ratio identity. Actual coefficient
positivity and the genuine source disk then justify the slit transfer.
The input source data are precisely the conclusions of StrongOptimalModel;
no uniform extraction or complex comparison is assumed. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma centeredGenerating_normalized_ratio (P:PsiTheory)(g p k:ℕ)(hp:1≤p)(hs:Stable g p)
    (x σ:ℝ)(hx:x∈Ico (0:ℝ) xCritical)(w:ℂ):
    centeredMarkedGenerating P g p k x σ w=
      Complex.exp (-(k:ℂ)*w/(σ:ℂ))*
        (normalizedMarkedGenerating P g p ((x:ℂ)*Complex.exp (w/(σ:ℂ)))/
          normalizedMarkedGenerating P g p (x:ℂ)):=by
  have hM0:(markedModel g p 0:ℂ)≠0:=by
    exact_mod_cast (markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  have hpi:(Real.pi:ℂ)≠0:=by exact_mod_cast Real.pi_ne_zero
  have hF:iteratedDeriv p (Phi P g) (x:ℂ)≠0:=by
    rw[marked_generating_value_real P g p hs x hx]
    exact_mod_cast (markedF_positive_cusp_weight P g p hp hs x hx).ne'
  unfold centeredMarkedGenerating normalizedMarkedGenerating
  field_simp

lemma origin_actual_centered_complex_comparison_of_source (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(S Bc:ℂ→ℂ)(ρs:ℝ)
    (hρs:0<ρs)(hρsx:ρs<xCritical)
    (hS:AnalyticAt ℂ S 0)(hSd:deriv S 0=2)(hBc:AnalyticAt ℂ Bc 0)(hBc0:Bc 0≠0)
    (hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ))
    (hBr:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ))
    (hmap:∀z:ℂ,‖z‖≤ρs→PositiveConvolution.planarInverse P z∈Ω):
    ∃η ρ D E K:ℝ,0<η ∧ η<ρs ∧ 0<ρ ∧ 0<D ∧ 0<E ∧ 0<K ∧
      (∀x∈Ioo (0:ℝ) η,Psi x≤K*x) ∧
      ∀g k J:ℕ,Stable g p→0<(complexity g p:ℝ)→
      (∀z∈Ω,1/2≤‖finiteMarkedFactor L (complexity g p:ℝ) J z‖ ∧
        ‖finiteMarkedFactor L (complexity g p:ℝ) J z‖≤2)→
      (∀z:ℂ,‖z‖≤ρs→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z)→
      ∀ε:ℝ,0<ε→ε≤1/2→
      (∀y∈Icc (0:ℝ) ρs,normalizedFiniteMarkedModel P g p S Bc L J (y:ℂ)≠0 ∧
        ‖normalizedMarkedGenerating P g p (y:ℂ)/normalizedFiniteMarkedModel P g p S Bc L J (y:ℂ)-1‖≤ε)→
      ∀x∈Ioo (0:ℝ) η,(k:ℝ)=(complexity g p:ℝ)*Psi x→
      ∀r:ℝ,0<r→16*r<ρ*Real.sqrt ((complexity g p:ℝ)*x)→∀w:ℂ,‖w‖≤3*r/2→
      let h:ℝ:=complexity g p
      let σ:ℝ:=Real.sqrt (h*euler Psi x)
      ‖centeredMarkedGenerating P g p k x σ w-centeredOriginFiniteModel P g p J S Bc L x w‖≤
        4*Real.sqrt ε*(D*Real.exp (E*(16*r)^2)):=by
  obtain ⟨η,ρ,E,D,K,hη,hηs,hρ,hE,hD,hK,hmean,hgrowth⟩:=
    origin_finite_model_growth_of_source P p Ω L S Bc ρs hρs hρsx hS hSd hBc hBc0 hSr hBr hmap
  refine ⟨η,ρ,D,E,K,hη,hηs,hρ,hD,hE,hK,(fun x hx=>(hmean x hx).2),?_⟩
  intro g k J hs hh hP hMa ε hε hεhalf hrel x hx hk r hr h16 w hw
  dsimp only
  let h:ℝ:=complexity g p
  let σ:ℝ:=Real.sqrt (h*euler Psi x)
  let N:ℂ→ℂ:=normalizedMarkedGenerating P g p
  let F:ℂ→ℂ:=centeredMarkedGenerating P g p k x σ
  let M:ℂ→ℂ:=centeredOriginFiniteModel P g p J S Bc L x
  let M0:ℂ→ℂ:=normalizedFiniteMarkedModel P g p S Bc L J
  let Z:ℂ→ℂ:=fun w=>(x:ℂ)*Complex.exp (w/(σ:ℂ))
  have hxc:x∈Ico (0:ℝ) xCritical:=⟨hx.1.le,hx.2.trans (hηs.trans hρsx)⟩
  have hnbase:‖(x:ℂ)‖≤ρs:=by rw[Complex.norm_of_nonneg hx.1.le];exact hx.2.le.trans hηs.le
  have hbase:x∈Icc (0:ℝ) ρs:=⟨hx.1.le,hx.2.le.trans hηs.le⟩
  have hgrowthx:=hgrowth g J hh hP hMa x hx
  have hMa':AnalyticOnNhd ℂ M (Metric.ball 0 (16*r)):=hgrowthx.1.mono (Metric.ball_subset_ball h16.le)
  have hdomain(z:ℂ)(hz:‖z‖<16*r):‖Z z‖≤ρs:=
    (hgrowthx.2 z (hz.le.trans h16.le)).2
  have htilt(z:ℂ)(hz:‖z‖<16*r):x*Real.exp (z.re/σ)≤ρs:=by
    have ht:=hdomain z hz
    change ‖(x:ℂ)*Complex.exp (z/(σ:ℂ))‖≤ρs at ht
    rw[norm_mul,Complex.norm_of_nonneg hx.1.le,Complex.norm_exp,Complex.div_ofReal_re] at ht
    exact ht
  have hFa:AnalyticOnNhd ℂ F (Metric.ball 0 (16*r)):=
    centeredMarkedGenerating_analytic_disk P g p k x σ (16*r) hx.1.le
      (fun z hz=>(htilt z hz).trans_lt hρsx)
  have hMb:∀z:ℂ,‖z‖<16*r→‖M z‖≤D*Real.exp (E*(16*r)^2):=by
    intro z hz
    apply (hgrowthx.2 z (hz.le.trans h16.le)).1.trans
    apply mul_le_mul_of_nonneg_left _ hD.le
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz.le 2) hE.le)
  have hpos:∀z:ℂ,‖z‖<16*r→‖F z‖≤‖F (z.re:ℂ)‖:=by
    intro z hz
    exact centeredMarkedGenerating_norm_domination P g p k hp hs x σ hxc z
      ⟨mul_nonneg hx.1.le (Real.exp_pos _).le,(htilt z hz).trans_lt hρsx⟩
  let e0:ℂ:=N (x:ℂ)/M0 (x:ℂ)-1
  have he0:‖e0‖≤ε:=(hrel x hbase).2
  have hreal:∀u:ℝ,|u|<16*r→∃e:ℂ,‖e‖≤ε ∧ F (u:ℂ)=M (u:ℂ)*((1+e)/(1+e0)):=by
    intro u hu
    let xt:ℝ:=x*Real.exp (u/σ)
    have hxt0:0<xt:=mul_pos hx.1 (Real.exp_pos _)
    have hxt:xt∈Icc (0:ℝ) ρs:=⟨hxt0.le,htilt (u:ℂ) (by simpa only[Complex.norm_real,Real.norm_eq_abs] using hu)⟩
    let e:ℂ:=N (xt:ℂ)/M0 (xt:ℂ)-1
    have heb:‖e‖≤ε:=(hrel xt hxt).2
    have hn0:N (x:ℂ)≠0:=by
      unfold N normalizedMarkedGenerating
      apply div_ne_zero
      · apply mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
        rw[marked_generating_value_real P g p hs x hxc]
        exact_mod_cast (markedF_positive_cusp_weight P g p hp hs x hxc).ne'
      · exact_mod_cast (markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
    have hM0:M0 (x:ℂ)≠0:=(hrel x hbase).1
    have hMt:M0 (xt:ℂ)≠0:=(hrel xt hxt).1
    have heq:=Analysis.centered_ratio_algebra
      (Complex.exp (-(k:ℂ)*(u:ℂ)/(σ:ℂ))) (N (xt:ℂ)) (N (x:ℂ)) (M0 (xt:ℂ)) (M0 (x:ℂ)) 1 1
      hn0 hMt hM0 (by norm_num) (by norm_num)
    simp only[div_one] at heq
    refine ⟨e,heb,?_⟩
    have hzc:Z (u:ℂ)=(xt:ℂ):=by
      dsimp[Z,xt]
      rw[←Complex.ofReal_div,←Complex.ofReal_exp,←Complex.ofReal_mul]
    have hc:(k:ℂ)=(h:ℂ)*(Psi x:ℂ):=by exact_mod_cast hk
    have hcenter:-(k:ℂ)*(u:ℂ)/(σ:ℂ)=-(h:ℂ)*(Psi x:ℂ)*((u:ℂ)/(σ:ℂ)):=by rw[hc];ring
    have hratio:=centeredGenerating_normalized_ratio P g p k hp hs x σ hxc (u:ℂ)
    dsimp only[F,M]
    rw[hratio]
    unfold centeredOriginFiniteModel
    change Complex.exp (-(k:ℂ)*(u:ℂ)/(σ:ℂ))*(N (Z (u:ℂ))/N (x:ℂ))=_
    rw[hzc]
    dsimp only[e,e0] at *
    rw[hcenter] at heq ⊢
    dsimp only[Z,σ,h,M0] at hzc heq ⊢
    rw[hzc]
    simpa only[mul_one] using heq
  exact Analysis.centered_slit_comparison F M r (D*Real.exp (E*(16*r)^2)) ε hr
    (by positivity) hε hεhalf hFa hMa' hMb hpos e0 he0 hreal w hw
end WP.HigherOrder
