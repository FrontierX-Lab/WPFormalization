import WPFormalization.Volumes.LocalComparisonModel
/-! The genuine critical finite model, its analytic continuation, exact finite
real recipe and slit comparison, for every retained finite order. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.local_comparison_critical_chart
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
      ∀r:ℝ,0<r→16*r<R*Real.sqrt (complexity g p:ℝ)→
      ∃M:ℂ→ℂ,
        HigherOrder.IsLocalFiniteMarkedModel P g p k J (XR (y₀-δ)) (16*r) M ∧
        (∀w:ℂ,‖w‖≤3*r/2→
          ‖centeredMarkedGenerating P g p k (XR (y₀-δ))
            (Real.sqrt ((complexity g p:ℝ)*euler Psi (XR (y₀-δ)))) w-M w‖≤
              4*Real.sqrt ε*(D*Real.exp (E*(16*r)^2))) ∧
        r≤Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi (XR (y₀-δ))):=by
  obtain ⟨Q,Rm,D,E,hQa,hQ0,hQphys,hRm,hD,hE,hmodel⟩:=
    d.centered_finite_model_uniform_bound p Ω L C B hΩ (hcover y₀ ⟨y₀_pos.le,le_rfl⟩) hC hB hLa hLb
  obtain ⟨Rr,hRr,hRry,hreal⟩:=d.actual_centered_real_comparison P p hp Q L hQphys (fun Y hY j=>hLr j Y hY)
  obtain ⟨Rl,Cl,hRl,hRly,hCl,hlens⟩:=d.standardized_lens_and_phase_bound P
  obtain ⟨Rt,hRt,hRty,htrace⟩:=d.centered_finite_model_real_trace P p Q L hQphys (fun Y hY j=>hLr j Y hY)
  obtain ⟨Rv,b,hRv,hRvy,hb,hvar⟩:=d.critical_variance_sqrt_lower
  let R:ℝ:=min Rm (min Rr (min Rl (min Rt (min Rv (Real.pi*b)))))
  have hR:0<R:=lt_min hRm (lt_min hRr (lt_min hRl (lt_min hRt (lt_min hRv (mul_pos Real.pi_pos hb)))))
  have hRm':R≤Rm:=min_le_left _ _
  have hRr':R≤Rr:=(min_le_right _ _).trans (min_le_left _ _)
  have hRl':R≤Rl:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRt':R≤Rt:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hRv':R≤Rv:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hRb:R≤Real.pi*b:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hRy:R<y₀:=hRl'.trans_lt hRly
  refine ⟨Q,R,D,E,hQa,hQ0,hQphys,hR,hRy,hD,hE,?_⟩
  intro δ hδ g k J hs hh hk hbudget hPnorm ε hε hεhalf hrel r hr h16
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
  refine ⟨M,⟨hMa,?_⟩,?_,?_⟩
  · intro u hu
    have ht:=htrace δ ⟨hδ.1,hδ.2.trans_le hRt'⟩ g k J hs hh hk u
      (hu.trans_le (h16.le.trans (mul_le_mul_of_nonneg_right hRt' hsqrt.le)))
    refine ⟨ht.1,?_⟩
    simpa only[HigherOrder.localFiniteMarkedTrace,
      inverseY_eq_of_root _ _ hY.2.le rfl] using ht.2
  · intro w hw
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
  · have hvb:=hvar δ ⟨hδ.1,hδ.2.trans_le hRv'⟩
    have hbound:R*Real.sqrt h≤Real.pi*Real.sqrt (h*euler Psi x):=by
      rw[Real.sqrt_mul hh.le]
      calc
        R*Real.sqrt h≤(Real.pi*b)*Real.sqrt h:=mul_le_mul_of_nonneg_right hRb hsqrt.le
        _≤Real.pi*(Real.sqrt h*Real.sqrt (euler Psi x)):=by
          have ht:=mul_le_mul_of_nonneg_left hvb (mul_nonneg Real.pi_pos.le hsqrt.le)
          nlinarith
    have ht:=h16.le.trans hbound
    linarith

end WP.Analysis
