import WPFormalization.Volumes.OriginTrueComparison
import WPFormalization.Volumes.CompactTrueComparison
import WPFormalization.Volumes.CriticalFourierGeometry
import WPFormalization.Volumes.MarkedFourierIntegralTail
import WPFormalization.Analysis.FourierCentralModelTransfer
/-! The original fixed-order local model in Lemma D.2. Its real trace is
the genuine finite marked model, with the actual canonical coefficients.
The complex model is its analytic continuation on the central disk. -/
noncomputable section
namespace WP.HigherOrder
open Set MeasureTheory

def localFiniteMarkedTrace (P:PsiTheory)(g p k K:ℕ)(x u:ℝ):ℂ:=
  let h:ℝ:=complexity g p
  let σ:=Real.sqrt (h*euler Psi x)
  let xt:=x*Real.exp (u/σ)
  Complex.exp (-(k:ℂ)*(u:ℂ)/(σ:ℂ))*
    ((markedModel g p (inverseY xt)/markedModel g p (inverseY x)*
      realFiniteMarkedFactor P p h K (inverseY xt)/
        realFiniteMarkedFactor P p h K (inverseY x):ℝ):ℂ)

def IsLocalFiniteMarkedModel (P:PsiTheory)(g p k K:ℕ)(x R:ℝ)(M:ℂ→ℂ):Prop:=
  AnalyticOnNhd ℂ M (Metric.ball 0 R) ∧
  ∀u:ℝ,|u|<R→
    x*Real.exp (u/Real.sqrt ((complexity g p:ℝ)*euler Psi x))∈Ioo (0:ℝ) xCritical ∧
    M (u:ℂ)=localFiniteMarkedTrace P g p k K x u

lemma IsLocalFiniteMarkedModel.eqOn (P:PsiTheory)(g p k K:ℕ)(x R:ℝ)(M N:ℂ→ℂ)
    (hR:0<R)(hM:IsLocalFiniteMarkedModel P g p k K x R M)
    (hN:IsLocalFiniteMarkedModel P g p k K x R N):
    Set.EqOn M N (Metric.ball 0 R):=by
  apply Analysis.complex_identity_of_real_germ M N _ 0 hM.1 hN.1
    (convex_ball (0:ℂ) R).isPreconnected (by simpa using (Metric.mem_ball_self hR:(0:ℂ)∈Metric.ball 0 R))
  filter_upwards[Metric.ball_mem_nhds (0:ℝ) hR] with u hu
  have hu':|u|<R:=by simpa only[Metric.mem_ball,Real.dist_eq,sub_zero] using hu
  exact (hM.2 u hu').2.trans (hN.2 u hu').2.symm

lemma local_comparison_fourier_transfer (P:PsiTheory)(g p k:ℕ)
    (hp:1≤p)(hs:Stable g p)(hh:0<complexity g p)
    (x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)
    (hk:(k:ℝ)=(complexity g p:ℝ)*Psi x)
    (M:ℂ→ℂ)(T E R:ℝ)(hT:0<T)
    (hMa:AnalyticOnNhd ℂ M (Metric.ball 0 (2*T)))
    (hperiod:T≤Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x))
    (hpoint:∀t∈Icc (-T) T,
      ‖centeredMarkedGenerating P g p k x
        (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) (Complex.I*(t:ℂ))-
          M (Complex.I*(t:ℂ))‖≤E)
    (htail:(∫t:ℝ in (Icc (-T) T)ᶜ,‖scaledMarkedFourier P g p x t‖)≤R):
    ‖((Real.sqrt ((complexity g p:ℝ)*euler Psi x)*cuspMass P g p k x:ℝ):ℂ)-
      ((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ in Icc (-T) T,M (Complex.I*(t:ℂ)))‖≤
        (R+2*T*E)/(2*Real.pi):=by
  have hMi:IntegrableOn (fun t:ℝ=>M (Complex.I*(t:ℂ))) (Icc (-T) T):=by
    apply ContinuousOn.integrableOn_Icc
    apply hMa.continuousOn.comp (by fun_prop:ContinuousOn (fun t:ℝ=>Complex.I*(t:ℂ)) (Icc (-T) T))
    intro t ht
    rw[Metric.mem_ball,dist_zero_right,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (abs_le.mpr ht).trans_lt (by linarith)
  have hpt:∀t∈Icc (-T) T,‖scaledMarkedFourier P g p x t-M (Complex.I*(t:ℂ))‖≤E:=by
    intro t ht
    rw[Analysis.scaledMarkedFourier_eq_centered_on_period P g p k x t hk
      ⟨(neg_le_neg hperiod).trans ht.1,ht.2.trans hperiod⟩]
    exact hpoint t ht
  have hi:=Analysis.integral_sub_local_model_norm (scaledMarkedFourier P g p x)
    (fun t:ℝ=>M (Complex.I*(t:ℂ))) T E R hT.le
    (scaledMarkedFourier_integrable P g p x hx) hMi hpt htail
  have hinv:=cuspMass_scaled_fourier P g p hp hs hh x hx (k:ℤ)
  simp only[Nat.cast_nonneg,ite_true,Int.toNat_natCast,Int.cast_natCast,hk,sub_self,
    zero_div,Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,one_mul] at hinv
  rw[hinv,←mul_sub,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity:0<2*Real.pi)]
  exact (mul_le_mul_of_nonneg_left hi (by positivity:(0:ℝ)≤(2*Real.pi)⁻¹)).trans_eq (by ring)
end WP.HigherOrder
