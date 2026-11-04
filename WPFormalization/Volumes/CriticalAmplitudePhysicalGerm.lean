import WPFormalization.Volumes.CriticalPhasePhysicalGerm
import WPFormalization.Volumes.ExtractionMorseComparison
/-! The same actual critical coordinate data and canonical coefficient
family agree, as complex germs, with every physical log-amplitude and
coefficient germ. The common critical interval precedes all indices.
The post-Morse statement retains the actual derivative of d.U. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma extractionB_ratio_parameter (p:ℕ)(Y Z:ℝ)
    (hY:Y∈Ico (0:ℝ) y₀)(hZ:Z∈Ico (0:ℝ) y₀):
    extractionB p (XR Z)/extractionB p (XR Y)=
      (Real.rpow (r Z) ((p:ℝ)/2)*Real.sqrt (WP.A Z*Theta Z))/
        (Real.rpow (r Y) ((p:ℝ)/2)*Real.sqrt (WP.A Y*Theta Y)):=by
  have h0:(0:ℝ)∈Ico (0:ℝ) y₀:=⟨le_rfl,y₀_pos⟩
  have ha0:Real.rpow (r 0) ((p:ℝ)/2)*Real.sqrt (WP.A 0*Theta 0)≠0:=
    (marked_amplitude_pos p 0 h0).ne'
  have haY:Real.rpow (r Y) ((p:ℝ)/2)*Real.sqrt (WP.A Y*Theta Y)≠0:=
    (marked_amplitude_pos p Y hY).ne'
  have hinvY:inverseY (XR Y)=Y:=inverseY_eq_of_root _ _ hY.2.le rfl
  have hinvZ:inverseY (XR Z)=Z:=inverseY_eq_of_root _ _ hZ.2.le rfl
  obtain ⟨hr0,hs0⟩:=mul_ne_zero_iff.mp ha0
  obtain ⟨hrY,hsY⟩:=mul_ne_zero_iff.mp haY
  rw[extractionB,extractionB,hinvZ,hinvY]
  field_simp [hr0,hs0,hrY,hsY]

lemma CriticalGaussianCoordinateData.preMorseAmplitude_germ_of_physical_amplitudes
    (d:CriticalGaussianCoordinateData)(P:PsiTheory)(p:ℕ)(Q:ℂ→ℂ)(L:ℕ→ℂ→ℂ)
    (hQa:AnalyticAt ℂ Q 0)(hQ0:Q 0=1)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ))
    (Ω:Set ℂ)(hΩ:IsOpen Ω)(hcover:(y₀:ℂ)∈Ω)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ)):
    ∃R:ℝ,0<R ∧ R<y₀ ∧ ∀δ∈Ioo (0:ℝ) R,
      let x:ℝ:=XR (y₀-δ)
      ∀(B:ℂ→ℂ)(Γ:ℕ→ℂ→ℂ),AnalyticAt ℂ B (x:ℂ)→
        ((fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ)))→
        (∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
          (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
            (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ)))→
        ∀j,(fun u:ℂ=>d.preMorseAmplitude Q p L j ((δ:ℂ),u))=ᶠ[𝓝 0]
          extractionPremorseGermAmplitude B Γ x j:=by
  obtain ⟨Rt,hRt,hRty,htilt⟩:=d.real_tilt_parameters P
  obtain ⟨Ra,hRa,hRay,hamp,hmean,hphase⟩:=d.physical_amplitude_phase_neighborhood Q p hQphys
  let A:ℂ × ℂ→ℂ:=d.kernel.jointAmplitude Q p d.q
  let y:ℂ × ℂ→ℂ:=fun z=>(y₀:ℂ)-z.1*d.q z
  have hA:AnalyticAt ℂ A (0,0):=d.kernel.jointAmplitude_analytic Q hQa hQ0 p d.q d.q_analytic d.q_zero
  have hy:AnalyticAt ℂ y (0,0):=analyticAt_const.sub (analyticAt_fst.mul d.q_analytic)
  have hy0:y (0,0)=(y₀:ℂ):=by simp[y]
  have hyn:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),y z∈Ω:=by
    apply hy.continuousAt.tendsto.eventually
    simpa only[Filter.Eventually,Set.ofPred_mem_eq,hy0] using hΩ.mem_nhds hcover
  have hgood:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),AnalyticAt ℂ A z ∧ AnalyticAt ℂ y z ∧ y z∈Ω:=by
    filter_upwards[hA.eventually_analyticAt,hy.eventually_analyticAt,hyn] with z ha hy hz
    exact ⟨ha,hy,hz⟩
  obtain ⟨Rf,hRf,hFa⟩:=Metric.eventually_nhds_iff.mp hgood
  let R:ℝ:=min Rt (min (Ra/3) Rf)
  have hR:0<R:=lt_min hRt (lt_min (by positivity) hRf)
  have hRRt:R≤Rt:=min_le_left _ _
  have hRRa:R≤Ra/3:=(min_le_right _ _).trans (min_le_left _ _)
  have hRRf:R≤Rf:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R,hR,hRRt.trans_lt hRty,?_⟩
  intro δ hδ
  dsimp only
  let x:ℝ:=XR (y₀-δ)
  intro B Γ hB hBr hΓ j
  have hδRt:δ∈Ioo (0:ℝ) Rt:=⟨hδ.1,hδ.2.trans_le hRRt⟩
  have hδRa:δ∈Ioo (0:ℝ) Ra:=⟨hδ.1,by have he:=hδ.2.trans_le hRRa;linarith⟩
  have hpoint:=hFa (y:=((δ:ℂ),0)) (by
    change dist ((δ:ℂ),(0:ℂ)) (0:ℂ × ℂ)<Rf
    rw[Prod.dist_eq]
    change max (dist (δ:ℂ) (0:ℂ)) (dist (0:ℂ) (0:ℂ))<Rf
    rw[dist_zero_right,Complex.norm_of_nonneg hδ.1.le,dist_self,max_eq_left hδ.1.le]
    exact hδ.2.trans_le hRRf)
  have hleft:AnalyticAt ℂ (fun u:ℂ=>d.preMorseAmplitude Q p L j ((δ:ℂ),u)) 0:=by
    exact (hpoint.1.mul ((hLa j _ hpoint.2.2).comp hpoint.2.1)).curry_right
  let v:ℝ:=WP.euler WP.Psi x
  let c:ℂ:=Complex.I/(Real.sqrt v:ℂ)
  have harg:AnalyticAt ℂ (fun u:ℂ=>(x:ℂ)*Complex.exp (c*u)) 0:=by fun_prop
  have harg0:(x:ℂ)*Complex.exp (c*0)=(x:ℂ):=by simp
  have hright:AnalyticAt ℂ (extractionPremorseGermAmplitude B Γ x j) 0:=
    ((hB.comp_of_eq harg harg0).sub analyticAt_const).cexp.mul ((hΓ j).1.comp_of_eq harg harg0)
  apply complex_germ_identity_of_ray _ _ (-Complex.I) (by simp) hleft hright
  let xt:ℝ→ℝ:=fun t=>x*Real.exp (t/Real.sqrt v)
  have hxt:ContinuousAt xt 0:=by fun_prop
  have hxt0:xt 0=x:=by simp[xt]
  have htend:Tendsto xt (𝓝 0) (𝓝 x):=by simpa only[hxt0] using hxt.tendsto
  have hBt:∀ᶠt:ℝ in 𝓝 0,B (xt t:ℂ)=(Real.log (extractionB p (xt t)):ℂ):=htend.eventually hBr
  have hΓt:∀ᶠt:ℝ in 𝓝 0,Γ j (xt t:ℂ)=(HigherOrder.markedCoefficient P p j (inverseY (xt t)):ℂ):=
    htend.eventually (hΓ j).2
  have hBx:B (x:ℂ)=(Real.log (extractionB p x):ℂ):=hBr.self_of_nhds
  have hnear:∀ᶠt:ℝ in 𝓝 0,|t|<Rt:=by
    have hn:∀ᶠt:ℝ in 𝓝 0,t∈Metric.ball 0 Rt:=Metric.ball_mem_nhds (0:ℝ) hRt
    filter_upwards[hn] with t ht
    simpa only[Metric.mem_ball,Real.dist_eq,sub_zero] using ht
  filter_upwards[hBt,hΓt,hnear] with t hBt hΓt ht htp
  have he:=htilt δ hδRt 1 (by norm_num) t (by simpa using ht)
  dsimp only at he
  simp only[Real.sqrt_one,Complex.ofReal_one,div_one,one_mul] at he
  have htI:xt t∈Ioo (0:ℝ) xCritical:=he.1
  let ε:ℝ:=y₀-inverseY (xt t)
  have hepos:0<ε:=by have hh:=he.2.1;change δ/2≤ε at hh;linarith[hδ.1]
  have heupper:ε≤2*δ:=he.2.2.1
  have heRa:ε∈Ioo (0:ℝ) Ra:=⟨hepos,by have hh:=hδ.2.trans_le hRRa;linarith⟩
  have hq:(δ:ℂ)*d.q ((δ:ℂ),-Complex.I*(t:ℂ))=(ε:ℂ):=he.2.2.2
  have hY:y₀-δ∈Ico (0:ℝ) y₀:=⟨by linarith[hδ.2,hRRt.trans_lt hRty],by linarith[hδ.1]⟩
  have hZ:y₀-ε∈Ico (0:ℝ) y₀:=⟨by linarith[heRa.2,hRay],by linarith[hepos]⟩
  have hYε:y₀-ε=inverseY (xt t):=by dsimp[ε];ring
  have hXR:XR (y₀-ε)=xt t:=by
    rw[hYε]
    exact (inverseY_branch (xt t) ⟨htI.1.le,htI.2⟩).2
  have hxI:x∈Ico (0:ℝ) xCritical:=by
    refine ⟨XR_nonneg_interior _ hY,?_⟩
    exact XR_strictMonoOn hY.2.le (show y₀∈Iic y₀ from Set.mem_Iic.mpr le_rfl) hY.2
  have htilt:(x:ℂ)*Complex.exp (c*(-Complex.I*(t:ℂ)))=(xt t:ℂ):=by
    have hc:c*(-Complex.I*(t:ℂ))=((t/Real.sqrt v:ℝ):ℂ):=by
      dsimp[c]
      push_cast
      calc _ = -(Complex.I^2)*(t:ℂ)/(Real.sqrt v:ℂ):=by ring
           _ = _:=by rw[Complex.I_sq];ring
    rw[hc,←Complex.ofReal_exp,←Complex.ofReal_mul]
  have hampEq:=d.kernel.jointAmplitude_physical_at Q p d.q δ ε (-Complex.I*(t:ℂ)) hδ.1 hepos hq
    (hamp δ hδRa) (hamp ε heRa)
  have hBR:=extractionB_ratio_parameter p (y₀-δ) (y₀-ε) hY hZ
  rw[hXR] at hBR
  change extractionB p (xt t)/extractionB p x=_ at hBR
  have hExp:Complex.exp (B (xt t:ℂ)-B (x:ℂ))=((extractionB p (xt t)/extractionB p x:ℝ):ℂ):=by
    rw[hBt,hBx,←Complex.ofReal_sub,←Complex.ofReal_exp,Real.exp_sub,
      Real.exp_log (extractionB_pos_interior p (xt t) ⟨htI.1.le,htI.2⟩),
      Real.exp_log (extractionB_pos_interior p x hxI),Complex.ofReal_div]
  change d.kernel.jointAmplitude Q p d.q ((δ:ℂ),-Complex.I*(t:ℂ))*
      L j ((y₀:ℂ)-(δ:ℂ)*d.q ((δ:ℂ),-Complex.I*(t:ℂ)))=
    extractionPremorseGermAmplitude B Γ x j (-Complex.I*(t:ℂ))
  unfold extractionPremorseGermAmplitude
  rw[htilt,hExp,hq,←Complex.ofReal_sub,hLr j (y₀-ε) ⟨hZ.1,hZ.2.le⟩,hYε,hΓt,hampEq,←hBR]
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.modelAmplitude_germ_of_physical_amplitudes
    (d:CriticalGaussianCoordinateData)(P:PsiTheory)(p:ℕ)(Q:ℂ→ℂ)(L:ℕ→ℂ→ℂ)
    (hQa:AnalyticAt ℂ Q 0)(hQ0:Q 0=1)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ))
    (Ω:Set ℂ)(hΩ:IsOpen Ω)(hcover:(y₀:ℂ)∈Ω)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ)):
    ∃R:ℝ,0<R ∧ R<y₀ ∧ ∀δ∈Ioo (0:ℝ) R,
      let x:ℝ:=XR (y₀-δ)
      ∀(B:ℂ→ℂ)(Γ:ℕ→ℂ→ℂ),AnalyticAt ℂ B (x:ℂ)→
        ((fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ)))→
        (∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
          (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
            (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ)))→
        ∀j,(fun w:ℂ=>d.modelAmplitude Q p L j ((δ:ℂ),w))=ᶠ[𝓝 0]
          extractionMorseGermAmplitude B Γ x (fun w:ℂ=>d.U ((δ:ℂ),w)) j:=by
  obtain ⟨Ra,hRa,hRay,hpre⟩:=d.preMorseAmplitude_germ_of_physical_amplitudes P p Q L
    hQa hQ0 hQphys Ω hΩ hcover hLa hLr
  obtain ⟨Ru,hRu,hLaU,hqa,hUa,haxis,hfold,hnorm⟩:=d.common_neighborhood
  let R:ℝ:=min Ra Ru
  have hR:0<R:=lt_min hRa hRu
  refine ⟨R,hR,(min_le_left _ _).trans_lt hRay,?_⟩
  intro δ hδ
  dsimp only
  intro B Γ hB hBr hΓ j
  have hδa:δ∈Ioo (0:ℝ) Ra:=⟨hδ.1,hδ.2.trans_le (min_le_left _ _)⟩
  have hδu:‖(δ:ℂ)‖<Ru:=by rw[Complex.norm_of_nonneg hδ.1.le];exact hδ.2.trans_le (min_le_right _ _)
  have hU0:d.U ((δ:ℂ),0)=0:=(haxis _ hδu).2
  have hp:(δ:ℂ)∈Metric.ball (0:ℂ) Ru:=by simpa only[Metric.mem_ball,dist_zero_right] using hδu
  have hUanalytic:AnalyticAt ℂ d.U ((δ:ℂ),0):=hUa _ ⟨hp,Metric.mem_ball_self hRu⟩
  have ht:Tendsto (fun w:ℂ=>d.U ((δ:ℂ),w)) (𝓝 0) (𝓝 0):=by
    simpa only[hU0] using hUanalytic.curry_right.continuousAt.tendsto
  have he:=ht.eventually (hpre δ hδa B Γ hB hBr hΓ j)
  have hpair:Tendsto (fun w:ℂ=>((δ:ℂ),w)) (𝓝 0) (𝓝 ((δ:ℂ),0)):=
    continuous_const.continuousAt.prodMk continuous_id.continuousAt |>.tendsto
  filter_upwards[he,hpair.eventually hUanalytic.eventually_analyticAt] with w hw hUw
  change d.preMorseAmplitude Q p L j ((δ:ℂ),d.U ((δ:ℂ),w))*sndPartial d.U ((δ:ℂ),w)=
    extractionPremorseGermAmplitude B Γ (XR (y₀-δ)) j (d.U ((δ:ℂ),w))*
      deriv (fun w:ℂ=>d.U ((δ:ℂ),w)) w
  rw[hw,sndPartial_eq_deriv d.U ((δ:ℂ),w) hUw]
end WP.Analysis
