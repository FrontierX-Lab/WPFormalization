import WPFormalization.Volumes.CriticalModelFourierIntegral
import WPFormalization.Volumes.UniformCriticalMorseDomain
/-! The literal critical centered model on the Fourier axis is continuous and integrable on every common smaller quarter-power window, uniformly in every finite amplitude cutoff. These are actual analytic-domain consequences, not a model regularity assumption. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory
lemma CriticalGaussianCoordinateData.centered_model_fourier_value
    (d:CriticalGaussianCoordinateData)(Q:ℂ→ℂ)(p:ℕ)(f:ℕ→ℂ→ℂ)(h:ℝ)(J:ℕ)(δ:ℂ)(t:ℝ) :
    d.centeredFiniteMarkedModel Q p f h J δ (Complex.I*(t:ℂ))=
      Complex.exp ((h:ℂ)*d.kernel.centeredPhase d.L d.q (δ,((t/Real.sqrt h:ℝ):ℂ)))*
        finiteMorseAmplitude (fun s u=>d.preMorseAmplitude Q p f s (δ,u)) h J ((t/Real.sqrt h:ℝ):ℂ)/
          HigherOrder.finiteMarkedFactor f h J ((y₀:ℂ)-δ) := by
  dsimp only[CriticalGaussianCoordinateData.centeredFiniteMarkedModel]
  have hu:-Complex.I*(Complex.I*(t:ℂ))/(Real.sqrt h:ℂ)=((t/Real.sqrt h:ℝ):ℂ) := by
    calc _ = ((-Complex.I)*Complex.I)*(t:ℂ)/(Real.sqrt h:ℂ):=by ring
         _ = (t:ℂ)/(Real.sqrt h:ℂ):=by rw[neg_mul,Complex.I_mul_I,neg_neg,one_mul]
         _ = _:=by push_cast;rfl
  rw[hu]
  rfl

lemma CriticalGaussianCoordinateData.common_centered_model_fourier_integrability
    (d:CriticalGaussianCoordinateData) (Q:ℂ→ℂ) (p:ℕ) (f:ℕ→ℂ→ℂ)
    (Ω:Set ℂ) (C B:ℝ) (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1)
    (hΩ:IsOpen Ω) (hcover:(y₀:ℂ)∈Ω) (hC:0<C) (hB:0<B)
    (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hbound:∀j z,z∈Ω→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2) :
    ∃R ρ:ℝ,0<R ∧ 0<ρ ∧ ∀δ:ℂ,‖δ‖<R→∀τ∈Ioc (0:ℝ) ρ,
      ∀h:ℝ,1≤h→∀J:ℕ,IntegrableOn
        (fun t:ℝ=>d.centeredFiniteMarkedModel Q p f h J δ (Complex.I*(t:ℂ)))
        (Icc (-(τ*Real.sqrt (Real.sqrt h))) (τ*Real.sqrt (Real.sqrt h))) := by
  obtain ⟨W,ρ,R,S,D,Cw,hρ,hR,hS,hD,hCw,hρR,hρS,hdata⟩:=
    d.uniform_morse_model_domain Q p f Ω C B hQ hQ0 hΩ hcover hC hB hf hbound
  refine ⟨ρ,ρ,hρ,hρ,?_⟩
  intro δ hδ τ hτ h hh1 J
  have hh:0<h:=zero_lt_one.trans_le hh1
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hss:0<Real.sqrt (Real.sqrt h):=Real.sqrt_pos.mpr hs
  have hs1:1≤Real.sqrt h:=by simpa using Real.sqrt_le_sqrt hh1
  have hss1:1≤Real.sqrt (Real.sqrt h):=by simpa using Real.sqrt_le_sqrt hs1
  have hτ0:0<τ:=hτ.1
  let T:ℝ:=τ*Real.sqrt (Real.sqrt h)
  have hT:0<T:=mul_pos hτ0 hss
  have hscale:T/Real.sqrt h=τ/Real.sqrt (Real.sqrt h) := by
    have heq:Real.sqrt h=(Real.sqrt (Real.sqrt h))^2:=(Real.sq_sqrt (Real.sqrt_nonneg h)).symm
    calc _ = τ*Real.sqrt (Real.sqrt h)/(Real.sqrt (Real.sqrt h))^2:=congrArg (fun r:ℝ=>τ*Real.sqrt (Real.sqrt h)/r) heq
         _ = _:=by field_simp[hss.ne']
  obtain ⟨hφ,hU,hmap,hphase,ha,hb,htrans,hbnd,hend⟩:=hdata δ hδ
  have hm:MapsTo (fun t:ℝ=>((t/Real.sqrt h:ℝ):ℂ)) (Icc (-T) T) (Metric.ball 0 S) := by
    intro t ht
    rw[Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hs]
    have hnorm:|t|≤T:=abs_le.mpr ⟨by linarith[ht.1],ht.2⟩
    calc _ ≤ T/Real.sqrt h:=div_le_div_of_nonneg_right hnorm hs.le
         _ = τ/Real.sqrt (Real.sqrt h):=hscale
         _ ≤ τ:=div_le_self hτ0.le hss1
         _ < S:=hτ.2.trans_lt hρS
  have hpoint:Continuous (fun t:ℝ=>((t/Real.sqrt h:ℝ):ℂ)):=by fun_prop
  have hφc:ContinuousOn (fun t:ℝ=>d.kernel.centeredPhase d.L d.q (δ,((t/Real.sqrt h:ℝ):ℂ))) (Icc (-T) T):=
    hφ.continuousOn.comp hpoint.continuousOn hm
  have hac:ContinuousOn (fun t:ℝ=>finiteMorseAmplitude (fun s u=>d.preMorseAmplitude Q p f s (δ,u)) h J ((t/Real.sqrt h:ℝ):ℂ)) (Icc (-T) T) := by
    apply continuousOn_finsetSum (Finset.range (J+1))
    intro s hs
    exact ((ha s).continuousOn.comp hpoint.continuousOn hm).div_const _
  have hc:ContinuousOn (fun t:ℝ=>d.centeredFiniteMarkedModel Q p f h J δ (Complex.I*(t:ℂ))) (Icc (-T) T) := by
    have he:(fun t:ℝ=>d.centeredFiniteMarkedModel Q p f h J δ (Complex.I*(t:ℂ)))=
        (fun t:ℝ=>Complex.exp ((h:ℂ)*d.kernel.centeredPhase d.L d.q (δ,((t/Real.sqrt h:ℝ):ℂ)))*
          finiteMorseAmplitude (fun s u=>d.preMorseAmplitude Q p f s (δ,u)) h J ((t/Real.sqrt h:ℝ):ℂ)/
          HigherOrder.finiteMarkedFactor f h J ((y₀:ℂ)-δ)):=by funext t;exact d.centered_model_fourier_value Q p f h J δ t
    rw[he]
    exact ((Complex.continuous_exp.comp_continuousOn (hφc.const_mul _)).mul hac).div_const _
  exact hc.integrableOn_Icc
end WP.Analysis
