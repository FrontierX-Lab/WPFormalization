import WPFormalization.Volumes.CriticalModelTrace
import WPFormalization.Analysis.CenteredExponentialPhase
/-! The actual critical pre-Morse phase is the physical extraction action germ. A common radius precedes the physical distance and every supplied actual action germ. The identity is proved on the imaginary ray using genuine real tilts, then continued by the analytic identity principle. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma complex_germ_identity_of_ray (f g:ℂ→ℂ) (c:ℂ) (hc:c≠0)
    (hf:AnalyticAt ℂ f 0) (hg:AnalyticAt ℂ g 0)
    (he:∀ᶠt:ℝ in 𝓝 0,0<t→f (c*(t:ℂ))=g (c*(t:ℂ))) : f=ᶠ[𝓝 0] g := by
  have hrot:AnalyticAt ℂ (fun z:ℂ=>c*z) 0:=analyticAt_const.mul analyticAt_id
  have hfr:AnalyticAt ℂ (fun z:ℂ=>f (c*z)) 0:=hf.comp_of_eq hrot (by simp)
  have hgr:AnalyticAt ℂ (fun z:ℂ=>g (c*z)) 0:=hg.comp_of_eq hrot (by simp)
  have heq:=complex_germ_identity_of_real_right _ _ hfr hgr he
  have ht:Tendsto (fun z:ℂ=>z/c) (𝓝 0) (𝓝 0):=by
    simpa only[zero_div] using (show ContinuousAt (fun z:ℂ=>z/c) 0 from continuous_id.continuousAt.div_const c).tendsto
  have heq':∀ᶠz:ℂ in 𝓝 0,f (c*(z/c))=g (c*(z/c)):=ht.eventually heq
  have harg(z:ℂ):c*(z/c)=z:=by field_simp
  change ∀ᶠz:ℂ in 𝓝 0,f z=g z
  simpa only[harg] using heq'

lemma CriticalGaussianCoordinateData.centeredPhase_germ_of_physical_action
    (d:CriticalGaussianCoordinateData) (P:PsiTheory) (Q:ℂ→ℂ) (p:ℕ)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)) :
    ∃R:ℝ,0<R ∧ R<y₀ ∧ ∀δ∈Ioo (0:ℝ) R,
      let x:ℝ:=XR (y₀-δ)
      ∀S:ℂ→ℂ,AnalyticAt ℂ S (x:ℂ)→
        ((fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)))→
        complexEuler S (x:ℂ)=(WP.Psi x:ℂ)→
        (fun u:ℂ=>d.kernel.centeredPhase d.L d.q ((δ:ℂ),u))=ᶠ[𝓝 0]
          centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ)) := by
  obtain ⟨Rt,hRt,hRty,htilt⟩:=d.real_tilt_parameters P
  obtain ⟨Ra,hRa,hRay,hamp,hmean,hphase⟩:=d.physical_amplitude_phase_neighborhood Q p hQphys
  let F:ℂ × ℂ→ℂ:=d.kernel.centeredPhase d.L d.q
  have hF:AnalyticAt ℂ F (0,0):=d.kernel.centeredPhase_analytic d.L d.q d.L_analytic d.q_analytic d.q_zero
  obtain ⟨Rf,hRf,hFa⟩:=Metric.eventually_nhds_iff.mp hF.eventually_analyticAt
  let R:ℝ:=min Rt (min (Ra/3) Rf)
  have hR:0<R:=lt_min hRt (lt_min (by positivity) hRf)
  have hRRt:R≤Rt:=min_le_left _ _
  have hRRa:R≤Ra/3:=(min_le_right _ _).trans (min_le_left _ _)
  have hRRf:R≤Rf:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R,hR,hRRt.trans_lt hRty,?_⟩
  intro δ hδ
  dsimp only
  let x:ℝ:=XR (y₀-δ)
  intro S hS hSr hν
  have hδRt:δ∈Ioo (0:ℝ) Rt:=⟨hδ.1,hδ.2.trans_le hRRt⟩
  have hδRa:δ∈Ioo (0:ℝ) Ra:=⟨hδ.1,by have he:=hδ.2.trans_le hRRa;linarith⟩
  have hFδ:AnalyticAt ℂ (fun u:ℂ=>F ((δ:ℂ),u)) 0 := by
    apply (hFa (y:=((δ:ℂ),0)) ?_).curry_right
    change dist ((δ:ℂ),(0:ℂ)) (0:ℂ × ℂ)<Rf
    rw[Prod.dist_eq]
    change max (dist (δ:ℂ) (0:ℂ)) (dist (0:ℂ) (0:ℂ))<Rf
    rw[dist_zero_right,Complex.norm_of_nonneg hδ.1.le,dist_self,max_eq_left hδ.1.le]
    exact hδ.2.trans_le hRRf
  let v:ℝ:=WP.euler WP.Psi x
  let c:ℂ:=Complex.I/(Real.sqrt v:ℂ)
  have harg:AnalyticAt ℂ (fun u:ℂ=>(x:ℂ)*Complex.exp (c*u)) 0:=by fun_prop
  have hGa:AnalyticAt ℂ (centeredExponentialSlice S (x:ℂ) c) 0:=
    (((hS.comp_of_eq harg (by simp only[mul_zero,Complex.exp_zero,mul_one];rfl)).sub analyticAt_const).sub (by fun_prop))
  apply complex_germ_identity_of_ray _ _ (-Complex.I) (by simp) hFδ hGa
  let xt:ℝ→ℝ:=fun t=>x*Real.exp (t/Real.sqrt v)
  have hxt:ContinuousAt xt 0:=by fun_prop
  have hxt0:xt 0=x:=by simp[xt]
  have hSt:∀ᶠt:ℝ in 𝓝 0,S (xt t:ℂ)=(extractionS (xt t):ℂ) := by
    exact (show Tendsto xt (𝓝 0) (𝓝 x) from by simpa only[hxt0] using hxt.tendsto).eventually hSr
  have hSx:S (x:ℂ)=(extractionS x:ℂ):=hSr.self_of_nhds
  have hnear:∀ᶠt:ℝ in 𝓝 0,|t|<Rt:=by
    have hn:∀ᶠt:ℝ in 𝓝 0,t∈Metric.ball 0 Rt:=Metric.ball_mem_nhds (0:ℝ) hRt
    filter_upwards[hn] with t ht
    simpa only[Metric.mem_ball,Real.dist_eq,sub_zero] using ht
  filter_upwards[hSt,hnear] with t hSt ht htp
  have he:=htilt δ hδRt 1 (by norm_num) t (by simpa using ht)
  dsimp only at he
  simp only[Real.sqrt_one,mul_one,Complex.ofReal_one,div_one,one_mul] at he
  have htI:xt t∈Ioo (0:ℝ) xCritical:=he.1
  let ε:ℝ:=y₀-inverseY (xt t)
  have hepos:0<ε:=by have hh:=he.2.1;change δ/2≤ε at hh;linarith[hδ.1]
  have heupper:ε≤2*δ:=he.2.2.1
  have heRa:ε∈Ioo (0:ℝ) Ra:=⟨hepos,by have hh:=hδ.2.trans_le hRRa;linarith⟩
  have hq:(δ:ℂ)*d.q ((δ:ℂ),-Complex.I*(t:ℂ))=(ε:ℂ):=he.2.2.2
  have hXR:XR (y₀-ε)=xt t := by
    have hY:y₀-ε=inverseY (xt t):=by dsimp[ε];ring
    rw[hY]
    exact (inverseY_branch (xt t) ⟨htI.1.le,htI.2⟩).2
  have hp:=d.kernel.centeredPhase_physical_at d.L d.q δ ε (-Complex.I*(t:ℂ)) hδ.1 hq
    (hphase δ hδRa ε heRa)
  rw[hXR] at hp
  have hM:d.kernel.psiUnit (δ:ℂ)*d.L (δ:ℂ)=((WP.Psi x/Real.sqrt v:ℝ):ℂ):=hmean δ hδRa
  have htilt:(x:ℂ)*Complex.exp (c*(-Complex.I*(t:ℂ)))=(xt t:ℂ) := by
    have hc:c*(-Complex.I*(t:ℂ))=((t/Real.sqrt v:ℝ):ℂ):=by
      dsimp[c]
      push_cast
      calc _ = -(Complex.I^2)*(t:ℂ)/(Real.sqrt v:ℂ):=by ring
           _ = _:=by rw[Complex.I_sq];ring
    rw[hc,←Complex.ofReal_exp,←Complex.ofReal_mul]
  change d.kernel.centeredPhase d.L d.q ((δ:ℂ),-Complex.I*(t:ℂ))=centeredExponentialSlice S (x:ℂ) c (-Complex.I*(t:ℂ))
  rw[hp]
  unfold centeredExponentialSlice
  rw[htilt,hSt,hSx,hν]
  have hlin:Complex.I*d.kernel.psiUnit (δ:ℂ)*d.L (δ:ℂ)*(-Complex.I*(t:ℂ))=
      c*(-Complex.I*(t:ℂ))*(WP.Psi x:ℂ) := by
    calc _ = Complex.I*(d.kernel.psiUnit (δ:ℂ)*d.L (δ:ℂ))*(-Complex.I*(t:ℂ)):=by ring
         _ = _ := by rw[hM];dsimp[c];push_cast;ring
  rw[hlin]
  push_cast
  ring

end WP.Analysis
