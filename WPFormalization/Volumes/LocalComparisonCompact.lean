import WPFormalization.Volumes.LocalComparisonModel
import WPFormalization.Analysis.VarianceCompactLower
/-! Lemma D.2 compact chart wrapper.  The actual finite marked model,
its exact real trace, its analytic disk and the true-to-model estimate
are returned in ONE choice.  The native coefficient family and arbitrary
finite cutoff are preserved.  No model-comparison hypothesis is admitted. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma local_compact_centered_comparison_of_fixed_coefficients (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (a b:ℝ)(ha:0<a)(hab:a≤b)(hbc:b<xCritical)
    (Ωf:Set ℂ)(f:ℕ→ℂ→ℂ)(C₀ B:ℝ)(hΩf:IsOpen Ωf)
    (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ωf)(hC₀:0<C₀)(hB:0<B)
    (hFa:∀j,AnalyticOnNhd ℂ (f j) Ωf)
    (hfr:∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hfb:∀j z,z∈Ωf→‖f j z‖≤C₀*B^j*(j.factorial:ℝ)^2):
    ∃(S l Bc:ℂ→ℂ)(R D:ℝ),0<R ∧ 0<D ∧
      (∀x∈Icc a b,AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ l (x:ℂ) ∧
        (∀ᶠt:ℝ in 𝓝 x,S (t:ℂ)=(extractionS t:ℂ)) ∧
        complexEuler S (x:ℂ)=(WP.Psi x:ℂ) ∧
        ((complexEuler^[2]) S) (x:ℂ)=(WP.euler WP.Psi x:ℂ) ∧
        l (x:ℂ)=((Real.sqrt (WP.euler WP.Psi x))⁻¹:ℝ) ∧
        ∀ᶠq:ℂ in 𝓝 (x:ℂ),(l q)^2*((complexEuler^[2]) S) q=1) ∧
      (∀x∈Ico (0:ℝ) xCritical,AnalyticAt ℂ Bc (x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      ∀x∈Icc a b,∀g k J:ℕ,Stable g p→0<(complexity g p:ℝ)→
      (k:ℝ)=(complexity g p:ℝ)*Psi x→
      2*B*((J:ℝ)+1)^2≤(complexity g p:ℝ)→
      (∀Y∈Icc (0:ℝ) y₀,1/2≤‖HigherOrder.finiteMarkedFactor f (complexity g p:ℝ) J (Y:ℂ)‖)→
      ∀ε:ℝ,0<ε→ε≤1/2→
      (∀Y∈Ico (0:ℝ) y₀,
        |(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
          HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J Y-1|≤ε)→
      ∀r:ℝ,0<r→16*r<R*Real.sqrt (complexity g p:ℝ)→
      ∃M:ℂ→ℂ,
        HigherOrder.IsLocalFiniteMarkedModel P g p k J x (16*r) M ∧
        (∀w:ℂ,‖w‖≤3*r/2→
          ‖centeredMarkedGenerating P g p k x
              (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) w-M w‖≤
            4*Real.sqrt ε*(D*Real.exp ((16*r)^2))) ∧
        r≤Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x):=by
  obtain ⟨S,l,Bc,U,rU,C,hU,hUx,hrU,hC,hData,hBc,hAf,hProp⟩:=
    actual_compact_model_uniform_data_of_fixed_coefficients P p a b ha hab hbc Ωf f C₀ B hΩf hcover hC₀ hB hFa hfr hfb
  obtain ⟨Rt,hRt,htrace⟩:=compact_real_trace_uniform a b ha hab hbc S l
    (fun x hx=>(hData x hx).2.1) (fun x hx=>(hData x hx).2.2.1)
  obtain ⟨v,hv,hvbound⟩:=compact_eulerPsi_positive_lower a b ha hab hbc
  let R:ℝ:=min (min rU Rt) (Real.pi*Real.sqrt v)
  have hR:0<R:=lt_min (lt_min hrU hRt) (mul_pos Real.pi_pos (Real.sqrt_pos.mpr hv))
  have hRr:R≤rU:=(min_le_left _ _).trans (min_le_left _ _)
  have hRRt:R≤Rt:=(min_le_left _ _).trans (min_le_right _ _)
  have hRπ:R≤Real.pi*Real.sqrt v:=min_le_right _ _
  refine ⟨S,l,Bc,R,4*C,hR,by positivity,hData,hBc,?_⟩
  intro x hx g k J hs hh hk hbudget hPnorm ε hε hεhalf hrel r hr h16
  let h:ℝ:=complexity g p
  let σ:ℝ:=Real.sqrt (h*euler Psi x)
  let F:ℂ→ℂ:=centeredMarkedGenerating P g p k x σ
  let M:ℂ→ℂ:=compactCenteredFiniteModel P Bc S l f h J (x:ℂ)
  have hsqrt:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hxc:x∈Ico (0:ℝ) xCritical:=⟨(ha.trans_le hx.1).le,hx.2.trans_lt hbc⟩
  have hsource:=hData x hx
  have hfinite(Y:ℝ)(hYi:Y∈Icc (0:ℝ) y₀):
      HigherOrder.finiteMarkedFactor f h J (Y:ℂ)=(HigherOrder.realFiniteMarkedFactor P p h J Y:ℂ):=by
    unfold HigherOrder.finiteMarkedFactor HigherOrder.realFiniteMarkedFactor
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw[hfr j Y hYi]
  have hP:∀Y∈Icc (0:ℝ) y₀,HigherOrder.realFiniteMarkedFactor P p h J Y≠0:=by
    intro Y hYi hzero
    have hn:=hPnorm Y hYi
    rw[hfinite Y hYi,hzero,Complex.ofReal_zero,norm_zero] at hn
    norm_num at hn
  have hbase:1/2≤‖HigherOrder.finiteMarkedFactor f h J (PositiveConvolution.planarInverse P (x:ℂ))‖:=by
    rw[PositiveConvolution.planarInverse_ofReal P x hxc]
    exact hPnorm _ ⟨(inverseY_branch x hxc).1.1,(inverseY_branch x hxc).1.2.le⟩
  have hMdata:=compact_centered_finite_model_growth_at P Bc S l f (x:ℂ) R C B h J hR hC.le hB hh
    (fun u hu=>⟨(hProp _ (hUx x hx) u (hu.trans_le hRr)).1,(hProp _ (hUx x hx) u (hu.trans_le hRr)).2.1⟩)
    (by
      intro j u hu
      refine ⟨hAf j _ ⟨hUx x hx,?_⟩,(hProp _ (hUx x hx) u (hu.trans_le hRr)).2.2.2 j⟩
      simpa only[Metric.mem_ball,dist_zero_right] using hu.trans_le hRr)
    hbudget hbase
  have hMa:AnalyticOnNhd ℂ M (Metric.ball 0 (16*r)):=hMdata.1.mono (Metric.ball_subset_ball h16.le)
  have htilt(z:ℂ)(hz:‖z‖<16*r):x*Real.exp (z.re/σ)<xCritical:=by
    have hzR:‖z‖<R*Real.sqrt h:=hz.trans h16
    have hzu:‖-Complex.I*z/(Real.sqrt h:ℂ)‖<rU:=by
      rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hsqrt.le]
      exact ((div_lt_iff₀ hsqrt).mpr hzR).trans_le hRr
    have hd:‖compactModelPoint l ((x:ℂ),-Complex.I*z/(Real.sqrt h:ℂ))‖<xCritical:=
      (hProp _ (hUx x hx) _ hzu).2.2.1
    rw[compactModelPoint_standardized l h x z hh.le hsource.2.2.2.2.2.1,
      norm_mul,Complex.norm_of_nonneg hxc.1,Complex.norm_exp,Complex.div_ofReal_re] at hd
    exact hd
  have hFa:AnalyticOnNhd ℂ F (Metric.ball 0 (16*r)):=
    centeredMarkedGenerating_analytic_disk P g p k x σ (16*r) hxc.1 htilt
  have hMb:∀z:ℂ,‖z‖<16*r→‖M z‖≤(4*C)*Real.exp ((16*r)^2):=by
    intro z hz
    apply (hMdata.2 z (hz.trans h16)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity:0≤4*C)
    exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (norm_nonneg z) hz.le 2)
  have hpos:∀z:ℂ,‖z‖<16*r→‖F z‖≤‖F (z.re:ℂ)‖:=by
    intro z hz
    exact centeredMarkedGenerating_norm_domination P g p k hp hs x σ hxc z
      ⟨mul_nonneg hxc.1 (Real.exp_pos _).le,htilt z hz⟩
  have htraceM:∀u:ℝ,|u|<16*r→
      let xt:ℝ:=x*Real.exp (u/σ)
      xt∈Ico (0:ℝ) xCritical ∧ M (u:ℂ)=
        Complex.exp (-(k:ℂ)*(u:ℂ)/(σ:ℂ))*
          ((markedModel g p (inverseY xt)/markedModel g p (inverseY x)*
            HigherOrder.realFiniteMarkedFactor P p h J (inverseY xt)/
              HigherOrder.realFiniteMarkedFactor P p h J (inverseY x):ℝ):ℂ):=by
    intro u hu
    have hut:|u/Real.sqrt h|<Rt:=by
      rw[abs_div,abs_of_pos hsqrt]
      exact ((div_lt_iff₀ hsqrt).mpr (hu.trans h16)).trans_le hRRt
    have ht:=htrace x hx (u/Real.sqrt h) hut
    have hBt:=(hBc _ ⟨ht.1.1.le,ht.1.2⟩).2
    have hsx:S (x:ℂ)=(extractionS x:ℂ):=hsource.2.2.1.self_of_nhds
    have hstd:=compact_centered_finite_standard_trace P g p k J hs S l Bc f x u hh
      ⟨ha.trans_le hx.1,hx.2.trans_lt hbc⟩ ht.1 (by simpa only[one_div] using hsource.2.2.2.2.2.1)
      hsx ht.2 hsource.2.2.2.1 (hBc x hxc).2 hBt hfr hk
    exact ⟨⟨hstd.1.1.le,hstd.1.2⟩,hstd.2⟩
  have ht:=actual_centered_real_comparison_from_model_trace P g p k J hp hs x σ (16*r) ε M hxc hε.le hP hrel htraceM
  refine ⟨M,⟨hMa,?_⟩,?_,?_⟩
  · intro u hu
    have ht:=htraceM u hu
    refine ⟨⟨mul_pos (ha.trans_le hx.1) (Real.exp_pos _),ht.1.2⟩,?_⟩
    simpa only [HigherOrder.localFiniteMarkedTrace] using ht.2
  · intro w hw
    exact centered_slit_comparison F M r ((4*C)*Real.exp ((16*r)^2)) ε hr (by positivity)
      hε hεhalf hFa hMa hMb hpos _ ht.1 ht.2 w hw
  · have hsmall:r≤R*Real.sqrt h:=by linarith
    have hvx:Real.sqrt v≤Real.sqrt (WP.euler WP.Psi x):=Real.sqrt_le_sqrt (hvbound x hx)
    calc r≤R*Real.sqrt h:=hsmall
         _≤(Real.pi*Real.sqrt v)*Real.sqrt h:=mul_le_mul_of_nonneg_right hRπ hsqrt.le
         _≤Real.pi*Real.sqrt (h*WP.euler WP.Psi x):=by
           rw [Real.sqrt_mul hh.le]
           nlinarith [mul_le_mul_of_nonneg_left hvx (mul_nonneg Real.pi_pos.le hsqrt.le)]
end WP.Analysis
