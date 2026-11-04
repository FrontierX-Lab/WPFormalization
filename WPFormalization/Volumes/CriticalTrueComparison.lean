import WPFormalization.Volumes.CriticalModelTrace
import WPFormalization.Volumes.MarkedGeneratingPositivity
import WPFormalization.Analysis.SlitDiskComparison
/-! The actual centered marked generating function versus the actual
finite critical model. The exact physical real trace transports the proved
real relative error into a normalized error identity. Actual coefficient
positivity controls complex tilts, and the proved two-constants theorem
transfers the real exponential error to the common complex central disk.
The ordinary coefficient-family and real-bound inputs are supplied by the
proved same-choice optimal model package; no comparison is externalized. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma centered_ratio_algebra (z a a0 b b0 c c0:ℂ)
    (ha0:a0≠0)(hb:b≠0)(hb0:b0≠0)(hc:c≠0)(hc0:c0≠0):
    z*(a/a0)=(z*(b/b0*c/c0))*
      ((1+((a/b)/c-1))/(1+((a0/b0)/c0-1))):=by
  have hun(v:ℂ):1+(v-1)=v:=by ring
  rw[hun, hun]
  field_simp
  <;>ring
end WP.Analysis
namespace WP
open Set
lemma marked_generating_value_real (P:PsiTheory)(g p:ℕ)(hs:Stable g p)
    (x:ℝ)(hx:x∈Ico (0:ℝ) xCritical):
    iteratedDeriv p (Phi P g) (x:ℂ)=(markedF P g p x:ℂ):=by
  have he:=PositiveConvolution.Phi_iteratedDeriv_ofReal P g p hs x hx
  have hr:=congrArg Complex.re he
  have hr':shifted P g (List.replicate p 0) (inverseY x)=markedF P g p x:=by
    simpa only[markedF,Complex.ofReal_re] using hr.symm
  rw[he,hr']
end WP
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.actual_centered_real_comparison
    (d:CriticalGaussianCoordinateData)(P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Q:ℂ→ℂ)(L:ℕ→ℂ→ℂ)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ))
    (hL:∀Y∈Icc (0:ℝ) y₀,∀j,L j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ)):
    ∃R:ℝ,0<R ∧ R<y₀ ∧ ∀δ∈Ioo (0:ℝ) R,∀g k J:ℕ,Stable g p→
      0<(complexity g p:ℝ)→(k:ℝ)=(complexity g p:ℝ)*Psi (XR (y₀-δ))→
      ∀ε:ℝ,0≤ε→
      (∀Y∈Icc (0:ℝ) y₀,HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J Y≠0)→
      (∀Y∈Ico (0:ℝ) y₀,
        |(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
          HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J Y-1|≤ε)→
      let x:ℝ:=XR (y₀-δ)
      let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
      let e0:ℂ:=(((Real.pi*markedF P g p x/markedModel g p (y₀-δ))/
        HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J (y₀-δ)-1:ℝ):ℂ)
      ‖e0‖≤ε ∧ ∀u:ℝ,|u|<R*Real.sqrt (complexity g p:ℝ)→
        ∃e:ℂ,‖e‖≤ε ∧
          centeredMarkedGenerating P g p k x σ (u:ℂ)=
            d.centeredFiniteMarkedModel Q p L (complexity g p:ℝ) J (δ:ℂ) (u:ℂ)*
              ((1+e)/(1+e0)):=by
  obtain ⟨R,hR,hRy,htrace⟩:=d.centered_finite_model_real_trace P p Q L hQphys hL
  refine ⟨R,hR,hRy,?_⟩
  intro δ hδ g k J hs hh hk ε hε hP hrel
  dsimp only
  let h:ℝ:=complexity g p
  let x:ℝ:=XR (y₀-δ)
  let σ:ℝ:=Real.sqrt (h*euler Psi x)
  let Y:ℝ:=y₀-δ
  have hY:Y∈Ico (0:ℝ) y₀:=⟨by dsimp[Y];linarith[hδ.2],by dsimp[Y];linarith[hδ.1]⟩
  have hxc:x∈Ico (0:ℝ) xCritical:=by
    have hp0:0≤XR Y:=XR_nonneg_interior Y hY
    have hl:XR Y<xCritical:=XR_strictMonoOn hY.2.le (show y₀∈Iic y₀ from Set.mem_Iic.mpr le_rfl) hY.2
    exact ⟨hp0,hl⟩
  have e0bound:‖(((Real.pi*markedF P g p x/markedModel g p Y)/
      HigherOrder.realFiniteMarkedFactor P p h J Y-1:ℝ):ℂ)‖≤ε:=by
    simpa only[Complex.norm_real,Real.norm_eq_abs] using hrel Y hY
  refine ⟨e0bound,?_⟩
  intro u hu
  let xt:ℝ:=x*Real.exp (u/σ)
  have ht:=htrace δ hδ g k J hs hh hk u hu
  dsimp only at ht
  have hxt:xt∈Ico (0:ℝ) xCritical:=⟨ht.1.1.le,ht.1.2⟩
  have hYt:inverseY xt∈Ico (0:ℝ) y₀:=(inverseY_branch xt hxt).1
  let Yt:ℝ:=inverseY xt
  let e:ℂ:=(((Real.pi*markedF P g p xt/markedModel g p Yt)/
    HigherOrder.realFiniteMarkedFactor P p h J Yt-1:ℝ):ℂ)
  have heb:‖e‖≤ε:=by
    have he:=hrel Yt hYt
    rw[(inverseY_branch xt hxt).2] at he
    simpa only[e,Complex.norm_real,Real.norm_eq_abs] using he
  refine ⟨e,heb,?_⟩
  have hF0:markedF P g p x≠0:=(markedF_positive_cusp_weight P g p hp hs x hxc).ne'
  have hM0:markedModel g p Y≠0:=(markedModel_pos_parameter g p hs Y hY).ne'
  have hMt:markedModel g p Yt≠0:=(markedModel_pos_parameter g p hs Yt hYt).ne'
  have hP0:HigherOrder.realFiniteMarkedFactor P p h J Y≠0:=hP Y ⟨hY.1,hY.2.le⟩
  have hPt:HigherOrder.realFiniteMarkedFactor P p h J Yt≠0:=hP Yt ⟨hYt.1,hYt.2.le⟩
  have heq:=centered_ratio_algebra
    (Complex.exp (-(k:ℂ)*(u:ℂ)/(σ:ℂ)))
    ((Real.pi*markedF P g p xt:ℝ):ℂ) ((Real.pi*markedF P g p x:ℝ):ℂ)
    (markedModel g p Yt:ℂ) (markedModel g p Y:ℂ)
    (HigherOrder.realFiniteMarkedFactor P p h J Yt:ℂ) (HigherOrder.realFiniteMarkedFactor P p h J Y:ℂ)
    (by exact_mod_cast (mul_ne_zero Real.pi_ne_zero hF0))
    (by exact_mod_cast hMt) (by exact_mod_cast hM0) (by exact_mod_cast hPt) (by exact_mod_cast hP0)
  unfold centeredMarkedGenerating
  have htilt:((x:ℂ)*Complex.exp ((u:ℂ)/(σ:ℂ)))=(xt:ℂ):=by
    dsimp[xt]
    rw[←Complex.ofReal_div,←Complex.ofReal_exp,←Complex.ofReal_mul]
  rw[htilt,marked_generating_value_real P g p hs xt hxt,marked_generating_value_real P g p hs x hxc,ht.2]
  dsimp only[e]
  push_cast at heq ⊢
  have hpi:(Real.pi:ℂ)≠0:=by exact_mod_cast Real.pi_ne_zero
  have hf0c:(markedF P g p x:ℂ)≠0:=by exact_mod_cast hF0
  dsimp only[σ,h,x,Y,Yt] at heq ⊢
  convert heq using 1 <;>field_simp [hpi,hf0c] <;>ring
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.actual_centered_complex_comparison
    (d:CriticalGaussianCoordinateData)(P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B:ℝ)
    (hΩ:IsOpen Ω)(hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C)(hB:0<B)(hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃(Q:ℂ→ℂ)(R D E:ℝ),AnalyticAt ℂ Q 0 ∧ Q 0=1 ∧
      (∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)) ∧
      0<R ∧ R<y₀ ∧ 0<D ∧ 0<E ∧ ∀δ∈Ioo (0:ℝ) R,∀g k J:ℕ,Stable g p→
      0<(complexity g p:ℝ)→(k:ℝ)=(complexity g p:ℝ)*Psi (XR (y₀-δ))→
      2*B*((J:ℝ)+1)^2≤(complexity g p:ℝ)→
      (∀Y∈Icc (0:ℝ) y₀,1/2≤‖HigherOrder.finiteMarkedFactor L (complexity g p:ℝ) J (Y:ℂ)‖)→
      ∀ε:ℝ,0<ε→ε≤1/2→
      (∀Y∈Ico (0:ℝ) y₀,
        |(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
          HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J Y-1|≤ε)→
      ∀r:ℝ,0<r→16*r<R*Real.sqrt (complexity g p:ℝ)→∀w:ℂ,‖w‖≤3*r/2→
      let x:ℝ:=XR (y₀-δ)
      let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
      ‖centeredMarkedGenerating P g p k x σ w-
        d.centeredFiniteMarkedModel Q p L (complexity g p:ℝ) J (δ:ℂ) w‖≤
          4*Real.sqrt ε*(D*Real.exp (E*(16*r)^2)):=by
  obtain ⟨Q,Rm,D,E,hQa,hQ0,hQphys,hRm,hD,hE,hmodel⟩:=
    d.centered_finite_model_uniform_bound p Ω L C B hΩ (hcover y₀ ⟨y₀_pos.le,le_rfl⟩) hC hB hLa hLb
  obtain ⟨Rr,hRr,hRry,hreal⟩:=d.actual_centered_real_comparison P p hp Q L hQphys (fun Y hY j=>hLr j Y hY)
  obtain ⟨Rl,Cl,hRl,hRly,hCl,hlens⟩:=d.standardized_lens_and_phase_bound P
  let R:ℝ:=min Rm (min Rr Rl)
  have hR:0<R:=lt_min hRm (lt_min hRr hRl)
  have hRm':R≤Rm:=min_le_left _ _
  have hRr':R≤Rr:=(min_le_right _ _).trans (min_le_left _ _)
  have hRl':R≤Rl:=(min_le_right _ _).trans (min_le_right _ _)
  have hRy:R<y₀:=hRl'.trans_lt hRly
  refine ⟨Q,R,D,E,hQa,hQ0,hQphys,hR,hRy,hD,hE,?_⟩
  intro δ hδ g k J hs hh hk hbudget hPnorm ε hε hεhalf hrel r hr h16 w hw
  dsimp only
  let h:ℝ:=complexity g p
  let x:ℝ:=XR (y₀-δ)
  let σ:ℝ:=Real.sqrt (h*euler Psi x)
  let F:ℂ→ℂ:=centeredMarkedGenerating P g p k x σ
  let M:ℂ→ℂ:=d.centeredFiniteMarkedModel Q p L h J (δ:ℂ)
  have hsqrt:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hδnorm:‖(δ:ℂ)‖<R:=by rw[Complex.norm_of_nonneg hδ.1.le];exact hδ.2
  have hY:y₀-δ∈Ico (0:ℝ) y₀:=⟨by linarith[hδ.2],by linarith[hδ.1]⟩
  have hxc:x∈Ico (0:ℝ) xCritical:=by
    exact ⟨XR_nonneg_interior _ hY,XR_strictMonoOn hY.2.le (show y₀∈Iic y₀ from Set.mem_Iic.mpr le_rfl) hY.2⟩
  have hfinite(Y:ℝ)(hYi:Y∈Icc (0:ℝ) y₀):
      HigherOrder.finiteMarkedFactor L h J (Y:ℂ)=
        (HigherOrder.realFiniteMarkedFactor P p h J Y:ℂ):=by
    unfold HigherOrder.finiteMarkedFactor HigherOrder.realFiniteMarkedFactor
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw[hLr j Y hYi]
  have hP:∀Y∈Icc (0:ℝ) y₀,HigherOrder.realFiniteMarkedFactor P p h J Y≠0:=by
    intro Y hYi hzero
    have hn:=hPnorm Y hYi
    rw[hfinite Y hYi,hzero,Complex.ofReal_zero,norm_zero] at hn
    norm_num at hn
  have hMdata:=hmodel (δ:ℂ) (hδnorm.trans_le hRm') h hh J hbudget (by simpa only[Complex.ofReal_sub] using hPnorm _ ⟨hY.1,hY.2.le⟩)
  have h16m:16*r≤Rm*Real.sqrt h:=h16.le.trans (mul_le_mul_of_nonneg_right hRm' hsqrt.le)
  have hMa:AnalyticOnNhd ℂ M (Metric.ball 0 (16*r)):=hMdata.1.mono (Metric.ball_subset_ball h16m)
  have htilt(z:ℂ)(hz:‖z‖<16*r):x*Real.exp (z.re/σ)<xCritical:=by
    have hzR:‖z‖<Rl*Real.sqrt h:=hz.trans_le (h16.le.trans (mul_le_mul_of_nonneg_right hRl' hsqrt.le))
    have ht:=hlens δ ⟨hδ.1,hδ.2.trans_le hRl'⟩ h hh z hzR
    dsimp only at ht
    have hn:‖(x:ℂ)*Complex.exp (z/(σ:ℂ))‖=x*Real.exp (z.re/σ):=by
      rw[norm_mul,Complex.norm_of_nonneg hxc.1,Complex.norm_exp,Complex.div_ofReal_re]
    have htx:‖(x:ℂ)*Complex.exp (z/(σ:ℂ))‖<xCritical:=ht.1
    rw[hn] at htx
    exact htx
  have hFa:AnalyticOnNhd ℂ F (Metric.ball 0 (16*r)):=
    centeredMarkedGenerating_analytic_disk P g p k x σ (16*r) hxc.1 htilt
  have hMb:∀z:ℂ,‖z‖<16*r→‖M z‖≤D*Real.exp (E*(16*r)^2):=by
    intro z hz
    have hb:=hMdata.2 z (hz.trans_le h16m)
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hD.le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz.le 2) hE.le
  have hpos:∀z:ℂ,‖z‖<16*r→‖F z‖≤‖F (z.re:ℂ)‖:=by
    intro z hz
    exact centeredMarkedGenerating_norm_domination P g p k hp hs x σ hxc z
      ⟨mul_nonneg hxc.1 (Real.exp_pos _).le,htilt z hz⟩
  obtain ⟨e0,he0,hrealtrace⟩:=show ∃e0:ℂ,‖e0‖≤ε ∧
      ∀u:ℝ,|u|<16*r→∃e:ℂ,‖e‖≤ε ∧ F (u:ℂ)=M (u:ℂ)*((1+e)/(1+e0)) from by
    have ht:=hreal δ ⟨hδ.1,hδ.2.trans_le hRr'⟩ g k J hs hh hk ε hε.le hP hrel
    dsimp only at ht
    refine ⟨_,ht.1,?_⟩
    intro u hu
    exact ht.2 u (hu.trans_le (h16.le.trans (mul_le_mul_of_nonneg_right hRr' hsqrt.le)))
  exact centered_slit_comparison F M r (D*Real.exp (E*(16*r)^2)) ε hr (by positivity)
    hε hεhalf hFa hMa hMb hpos e0 he0 hrealtrace w hw
end WP.Analysis
