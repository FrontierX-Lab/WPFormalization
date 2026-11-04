import WPFormalization.HigherOrder.LocalComparisonSource
import WPFormalization.Volumes.LocalComparisonOrigin
import WPFormalization.Volumes.LocalComparisonCompact
import WPFormalization.Volumes.LocalComparisonCritical
import WPFormalization.Analysis.LocalComparisonRateWindow
import WPFormalization.Analysis.LocalComparisonRateRadius
/-! Lemma D.2 with one fixed retained order and the original logarithmic
cutoff. The locally analytic integrand is uniquely specified by the genuine
finite marked model, without requiring continuation to a whole cusp disk. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace WP.HigherOrder
open Set MeasureTheory

theorem local_comparison_proof (P:PsiTheory)(p:ℕ)(hp:1≤p):
    ∃Kc:ℕ,∃A₀ C₀ C H:ℝ,0<A₀ ∧ 0<C₀ ∧ 0<C ∧ 0<H ∧
      ∀g k:ℕ,H≤(complexity g p:ℝ)→∀x∈Ioo (0:ℝ) xCritical,
        (k:ℝ)=(complexity g p:ℝ)*Psi x→
        C₀*Real.log (complexity g p:ℝ)≤ min (complexity g p:ℝ) (k:ℝ)→
        let T:=Real.sqrt (A₀*Real.log (complexity g p:ℝ))
        T^2=A₀*Real.log (complexity g p:ℝ) ∧
        ∃M:ℂ→ℂ,IsLocalFiniteMarkedModel P g p k Kc x (16*T) M ∧
          ‖((Real.sqrt ((complexity g p:ℝ)*euler Psi x)*cuspMass P g p k x:ℝ):ℂ)-
            ((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ in Icc (-T) T,M (Complex.I*(t:ℂ)))‖≤
              C/(complexity g p:ℝ)^2:=by
  obtain ⟨Ω,L,Ca,B,cb,Hs,hΩ,hcover,hCa,hB,hcb,hHs,hLa,hL0,hLr,hLb,hsource⟩:=
    local_comparison_marked_source P p hp
  obtain ⟨η,Ro,Do,Eo,Km,hη,hηx,hRo,hDo,hEo,hKm,hmean,horigin⟩:=
    local_comparison_origin_chart P p hp Ω L Ca B hΩ hcover hCa hB hLa hLr hLb
  obtain ⟨d⟩:=Analysis.exists_criticalGaussianCoordinateData
  obtain ⟨Q,Rc,Dc,Ec,hQa,hQ0,hQp,hRc,hRcy,hDc,hEc,hcritical⟩:=
    d.local_comparison_critical_chart P p hp Ω L Ca B hΩ hcover hCa hB hLa hLr hLb
  let b:ℝ:=XR (y₀-Rc/2)
  have hYb:y₀-Rc/2∈Ioo (0:ℝ) y₀:=⟨by linarith,by linarith⟩
  have hb:0<b:=by
    simpa only[b,XR_zero] using XR_strictMonoOn y₀_pos.le hYb.2.le hYb.1
  have hbx:b<xCritical:=XR_strictMonoOn hYb.2.le (show y₀∈Iic y₀ from by simp) hYb.2
  let a:ℝ:=min (η/2) (b/2)
  have ha:0<a:=lt_min (half_pos hη) (half_pos hb)
  have haη:a<η:=(min_le_left _ _).trans_lt (half_lt_self hη)
  have hab:a≤b:=(min_le_right _ _).trans (by linarith)
  obtain ⟨S,l,Bc,Rm,Dm,hRm,hDm,hSdata,hBcdata,hcompact⟩:=
    Analysis.local_compact_centered_comparison_of_fixed_coefficients P p hp a b ha hab hbx
      Ω L Ca B hΩ hcover hCa hB hLa hLr hLb
  let R:ℝ:=min Ro (min Rc Rm)
  let D:ℝ:=max Do (max Dc Dm)
  let E:ℝ:=max Eo (max Ec 1)
  have hR:0<R:=lt_min hRo (lt_min hRc hRm)
  have hRRo:R≤Ro:=min_le_left _ _
  have hRRc:R≤Rc:=(min_le_right _ _).trans (min_le_left _ _)
  have hRRm:R≤Rm:=(min_le_right _ _).trans (min_le_right _ _)
  have hDoD:Do≤D:=le_max_left _ _
  have hDcD:Dc≤D:=(le_max_left _ _).trans (le_max_right _ _)
  have hDmD:Dm≤D:=(le_max_right _ _).trans (le_max_right _ _)
  have hEoE:Eo≤E:=le_max_left _ _
  have hEcE:Ec≤E:=(le_max_left _ _).trans (le_max_right _ _)
  have h1E:1≤E:=(le_max_right _ _).trans (le_max_right _ _)
  have hD:0<D:=hDo.trans_le hDoD
  have hE:0<E:=by linarith
  obtain ⟨ct,Ct,hct,hCt,htails⟩:=Analysis.actual_marked_fourier_integral_tails P
  obtain ⟨A,hA,N,K,hN,hKodd,hKN,hctA,hNE⟩:=
    Analysis.local_comparison_fixed_order_selection ct E hct hE
  let Dr:ℝ:=2*Ca*B^(K+1)*((K+1).factorial:ℝ)^2
  have hDr:0<Dr:=by dsimp[Dr];positivity
  obtain ⟨H,hH,hHbase,hbudget⟩:=Analysis.local_comparison_fixed_order_budget B cb Dr (max Hs 32) N K hB hcb hDr hN
  obtain ⟨Co,hCo,hwindowo⟩:=Analysis.local_comparison_radius_budget A R Km hA hR hKm
  obtain ⟨Cm,hCm,hwindowm⟩:=Analysis.local_comparison_radius_budget A R 1 hA hR zero_lt_one
  let C₀:ℝ:=max Co Cm
  let Cp:ℝ:=4*Real.sqrt Dr*D
  let C:ℝ:=(Ct+2*Cp)/(2*Real.pi)
  have hC₀:0<C₀:=hCo.trans_le (le_max_left _ _)
  have hCp:0<Cp:=by dsimp[Cp];positivity
  have hC:0<C:=by dsimp[C];positivity
  refine ⟨K,A,C₀,C,H,hA,hC₀,hC,hH,?_⟩
  intro g k hg x hx hk hw
  dsimp only
  let h:ℝ:=complexity g p
  let T:ℝ:=Real.sqrt (A*Real.log h)
  let ε:ℝ:=Dr/h^(2*N)
  have hbo:=hbudget h hg
  have hh2:2≤h:=hbo.1
  have hh:0<h:=by linarith
  have hh1:1≤h:=by linarith
  have hh32:32≤h:=(le_max_right _ _).trans (hHbase.trans hg)
  have hhn:0<complexity g p:=by exact_mod_cast (show 0<(complexity g p:ℝ) from hh)
  have hs:Stable g p:=by
    unfold Stable
    unfold complexity at hhn
    omega
  have hhs:Hs≤h:=(le_max_left _ _).trans (hHbase.trans hg)
  have hKbudget:2*B*((K:ℝ)+1)^2≤h:=by simpa only[Nat.cast_add,Nat.cast_one] using hbo.2.2.1
  have hsrc:=hsource g K hhs hbo.2.1 hKbudget
  have hPall:∀z∈Ω,1/2≤‖finiteMarkedFactor L h K z‖ ∧ ‖finiteMarkedFactor L h K z‖≤2:=
    fun z hz=>⟨(hsrc.1 z hz).2.1,(hsrc.1 z hz).2.2.1⟩
  have hPreal:∀Y∈Icc (0:ℝ) y₀,1/2≤‖finiteMarkedFactor L h K (Y:ℂ)‖:=
    fun Y hY=>(hPall _ (hcover Y hY)).1
  have hε:0<ε:=hbo.2.2.2.1
  have hεhalf:ε≤1/2:=hbo.2.2.2.2
  have hreal:∀Y∈Ico (0:ℝ) y₀,
      |(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/realFiniteMarkedFactor P p h K Y-1|≤ε:=by
    intro Y hY
    simpa only[ε,Dr,hKN] using hsrc.2.2 Y hY
  have hlog:0≤Real.log h:=Real.log_nonneg hh1
  have hwm:Cm*Real.log h≤ min h (k:ℝ):=
    (mul_le_mul_of_nonneg_right (le_max_right Co Cm) hlog).trans hw
  have hkh:(k:ℝ)≤1*h*((k:ℝ)/h):=by
    rw[one_mul,mul_div_cancel₀ _ hh.ne']
  have hwindow:=hwindowm h k ((k:ℝ)/h) hh2 hwm hkh
  have hT:0<T:=hwindow.1
  have hT2:T^2=A*Real.log h:=hwindow.2.1
  have hTsize:T^2≤h:=hwindow.2.2.1
  have hTh:T≤h:=hwindow.2.2.2.1
  have h16:16*T<R*Real.sqrt h:=hwindow.2.2.2.2.1
  have huniform (D₁ E₁:ℝ)(hD₁:0<D₁)(hD₁D:D₁≤D)(hE₁E:E₁≤E):
      4*Real.sqrt ε*(D₁*Real.exp (E₁*(16*T)^2))≤Cp/h^4:=by
    apply le_trans _ (Analysis.local_comparison_fixed_order_point_error A E D Dr h N hA hE hD hDr hh1 hNE)
    dsimp only[ε,T]
    gcongr
  obtain ⟨M,hmodel,hpoint,hperiod⟩:
      ∃M:ℂ→ℂ,IsLocalFiniteMarkedModel P g p k K x (16*T) M ∧
        (∀w:ℂ,‖w‖≤3*T/2→
          ‖centeredMarkedGenerating P g p k x (Real.sqrt (h*euler Psi x)) w-M w‖≤Cp/h^4) ∧
        T≤Real.pi*Real.sqrt (h*euler Psi x):=by
    by_cases hxo:x<η
    · have hxo':x∈Ioo (0:ℝ) η:=⟨hx.1,hxo⟩
      have hkx:(k:ℝ)≤Km*h*x:=by
        calc
          (k:ℝ)=h*Psi x:=hk
          _≤h*(Km*x):=mul_le_mul_of_nonneg_left (hmean x hxo') hh.le
          _=Km*h*x:=by ring
      have hwo:Co*Real.log h≤ min h (k:ℝ):=
        (mul_le_mul_of_nonneg_right (le_max_left Co Cm) hlog).trans hw
      have hwo':=hwindowo h k x hh2 hwo hkx
      obtain ⟨M,hM,hpM,hper⟩:=horigin g k K hs hh hPall ε hε hεhalf hreal x hxo' hk T hT
        (hwo'.2.2.2.2.2.trans_le (mul_le_mul_of_nonneg_right hRRo (Real.sqrt_nonneg _)))
      exact ⟨M,hM,fun w hw=>(hpM w hw).trans (huniform Do Eo hDo hDoD hEoE),hper⟩
    · by_cases hxm:x≤b
      · obtain ⟨M,hM,hpM,hper⟩:=hcompact x ⟨haη.le.trans (le_of_not_gt hxo),hxm⟩ g k K hs hh hk
          hKbudget hPreal ε hε hεhalf hreal T hT
          (h16.trans_le (mul_le_mul_of_nonneg_right hRRm (Real.sqrt_nonneg _)))
        exact ⟨M,hM,fun w hw=>(hpM w hw).trans (by simpa only[one_mul] using huniform Dm 1 hDm hDmD h1E),hper⟩
      · let δ:ℝ:=y₀-inverseY x
        have hY:=(inverseY_branch x ⟨hx.1.le,hx.2⟩).1
        have hδ0:0<δ:=sub_pos.mpr hY.2
        have hδR:δ<Rc:=by
          have hYb_lt:y₀-Rc/2< inverseY x:=by
            by_contra hn
            have hm:=XR_strictMonoOn.monotoneOn (show inverseY x∈Iic y₀ from hY.2.le)
              (show y₀-Rc/2∈Iic y₀ from hYb.2.le) (le_of_not_gt hn)
            rw[(inverseY_branch x ⟨hx.1.le,hx.2⟩).2] at hm
            exact hxm hm
          change y₀-inverseY x<Rc
          linarith only[hYb_lt,hRc]
        have hxeq:XR (y₀-δ)=x:=by
          dsimp[δ]
          rw[sub_sub_cancel,(inverseY_branch x ⟨hx.1.le,hx.2⟩).2]
        obtain ⟨M,hM,hpM,hper⟩:=hcritical δ ⟨hδ0,hδR⟩ g k K hs hh
          (by simpa only[hxeq] using hk) hKbudget hPreal ε hε hεhalf hreal T hT
          (h16.trans_le (mul_le_mul_of_nonneg_right hRRc (Real.sqrt_nonneg _)))
        rw[hxeq] at hM hpM hper
        exact ⟨M,hM,fun w hw=>(hpM w hw).trans (huniform Dc Ec hDc hDcD hEcE),hper⟩
  refine ⟨hT2,M,hmodel,?_⟩
  have htail:(∫t:ℝ in (Icc (-T) T)ᶜ,‖scaledMarkedFourier P g p x t‖)≤Ct/h^3:=by
    apply ((htails g p hp hs (by exact_mod_cast (show (32:ℝ)≤(complexity g p:ℝ) from hh32)) x hx).2 T hT.le hTsize).trans
    exact (mul_le_mul_of_nonneg_left
      (Analysis.local_comparison_gaussian_tail A ct h hA hct hh1 (by linarith)) hCt.le).trans_eq (by ring)
  have he:=local_comparison_fourier_transfer P g p k hp hs hhn x hx hk M T (Cp/h^4) (Ct/h^3) hT
    (hmodel.1.mono (Metric.ball_subset_ball (by linarith))) hperiod
    (by
      intro t ht
      apply hpoint
      rw[norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
      exact (abs_le.mpr ht).trans (by linarith)) htail
  apply he.trans
  have hnonneg:0≤Ct+2*Cp:=by positivity
  have hnum:Ct/h^3+2*T*(Cp/h^4)≤(Ct+2*Cp)/h^3:=by
    calc
      _≤Ct/h^3+2*h*(Cp/h^4):=by gcongr
      _=(Ct+2*Cp)/h^3:=by field_simp
  apply (div_le_div_of_nonneg_right hnum (by positivity:0≤2*Real.pi)).trans
  change (Ct+2*Cp)/h^3/(2*Real.pi)≤((Ct+2*Cp)/(2*Real.pi))/h^2
  have hpowers:h^2≤h^3:=pow_le_pow_right₀ hh1 (by norm_num)
  have hc:0≤(Ct+2*Cp)/(2*Real.pi):=by positivity
  calc
    _=((Ct+2*Cp)/(2*Real.pi))/h^3:=by ring
    _≤_:=div_le_div_of_nonneg_left hc (by positivity) hpowers
@[blueprint "lem:local-comparison"]
theorem local_comparison (P:PsiTheory)(p:ℕ)(hp:1≤p):
    ∃Kc:ℕ,∃A₀ C₀ C H:ℝ,0<A₀ ∧ 0<C₀ ∧ 0<C ∧ 0<H ∧
      ∀g k:ℕ,H≤(complexity g p:ℝ)→∀x∈Ioo (0:ℝ) xCritical,
        (k:ℝ)=(complexity g p:ℝ)*Psi x→
        C₀*Real.log (complexity g p:ℝ)≤ min (complexity g p:ℝ) (k:ℝ)→
        let T:=Real.sqrt (A₀*Real.log (complexity g p:ℝ))
        T^2=A₀*Real.log (complexity g p:ℝ) ∧
        ∃M:ℂ→ℂ,IsLocalFiniteMarkedModel P g p k Kc x (16*T) M ∧
          ‖((Real.sqrt ((complexity g p:ℝ)*euler Psi x)*cuspMass P g p k x:ℝ):ℂ)-
            ((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ in Icc (-T) T,M (Complex.I*(t:ℂ)))‖≤
              C/(complexity g p:ℝ)^2:=by
  exact local_comparison_proof P p hp
end WP.HigherOrder
