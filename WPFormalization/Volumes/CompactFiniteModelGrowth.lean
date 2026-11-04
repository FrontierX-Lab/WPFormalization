import WPFormalization.Volumes.CompactFixedCoefficients
import WPFormalization.Volumes.CompactModelRealTrace
import WPFormalization.Volumes.CriticalModelGrowth
/-! The literal finite compact pre-Morse model retains the given canonical
family and native order budget. Its common normalized disk growth bound
is proved from the actual phase and amplitude data. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

def compactCenteredFiniteModel (P:PsiTheory)(Bc S l:ℂ→ℂ)(f:ℕ→ℂ→ℂ)
    (h:ℝ)(J:ℕ)(x w:ℂ):ℂ:=
  Complex.exp ((h:ℂ)*centeredExponentialPhase S l (x,-Complex.I*w/(Real.sqrt h:ℂ)))*
    (∑j∈Finset.range (J+1),compactPremorseAmplitude P Bc l f j (x,-Complex.I*w/(Real.sqrt h:ℂ))/(h:ℂ)^j)/
      HigherOrder.finiteMarkedFactor f h J (PositiveConvolution.planarInverse P x)

lemma compact_centered_finite_model_growth_at (P:PsiTheory)(Bc S l:ℂ→ℂ)(f:ℕ→ℂ→ℂ)
    (x:ℂ)(r C B h:ℝ)(J:ℕ)(hr:0<r)(hC:0≤C)(hB:0<B)(hh:0<h)
    (hphase:∀u:ℂ,‖u‖<r→AnalyticAt ℂ (centeredExponentialPhase S l) (x,u) ∧
      ‖centeredExponentialPhase S l (x,u)‖≤‖u‖^2)
    (hamp:∀j u,‖u‖<r→AnalyticAt ℂ (compactPremorseAmplitude P Bc l f j) (x,u) ∧
      ‖compactPremorseAmplitude P Bc l f j (x,u)‖≤C*B^j*(j.factorial:ℝ)^2)
    (hbudget:2*B*((J:ℝ)+1)^2≤h)
    (hbase:1/2≤‖HigherOrder.finiteMarkedFactor f h J (PositiveConvolution.planarInverse P x)‖):
    AnalyticOnNhd ℂ (compactCenteredFiniteModel P Bc S l f h J x)
      (Metric.ball 0 (r*Real.sqrt h)) ∧
      ∀w:ℂ,‖w‖<r*Real.sqrt h→
        ‖compactCenteredFiniteModel P Bc S l f h J x w‖≤4*C*Real.exp (‖w‖^2):=by
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hu(w:ℂ):‖-Complex.I*w/(Real.sqrt h:ℂ)‖=‖w‖/Real.sqrt h:=by
    simp only[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg (Real.sqrt_nonneg h)]
  have hurn(w:ℂ)(hw:‖w‖<r*Real.sqrt h):‖-Complex.I*w/(Real.sqrt h:ℂ)‖<r:=by
    rw[hu]
    exact (div_lt_iff₀ hs).mpr hw
  have harg(w:ℂ):AnalyticAt ℂ (fun w:ℂ=>(x,-Complex.I*w/(Real.sqrt h:ℂ))) w:=by fun_prop
  constructor
  · intro w hw
    have hw':‖w‖<r*Real.sqrt h:=by simpa only[Metric.mem_ball,dist_zero_right] using hw
    unfold compactCenteredFiniteModel
    apply AnalyticAt.div_const
    apply AnalyticAt.mul
    · exact (analyticAt_const.mul ((hphase _ (hurn w hw')).1.comp (f:=fun w:ℂ=>(x,-Complex.I*w/(Real.sqrt h:ℂ))) (harg w))).cexp
    · apply Finset.analyticAt_fun_sum
      intro j hj
      exact ((hamp j _ (hurn w hw')).1.comp (f:=fun w:ℂ=>(x,-Complex.I*w/(Real.sqrt h:ℂ))) (harg w)).div_const
  · intro w hw
    have hwu:=hurn w hw
    have hsum:=finite_gevrey_two_sum_norm
      (fun j=>compactPremorseAmplitude P Bc l f j (x,-Complex.I*w/(Real.sqrt h:ℂ))) C B h J
      hC hB hh (fun j=>(hamp j _ hwu).2) hbudget
    have hex:‖Complex.exp ((h:ℂ)*centeredExponentialPhase S l (x,-Complex.I*w/(Real.sqrt h:ℂ)))‖≤Real.exp (‖w‖^2):=by
      apply (Complex.norm_exp_le_exp_norm _).trans
      apply Real.exp_le_exp.mpr
      rw[norm_mul,Complex.norm_of_nonneg hh.le]
      have ht:=mul_le_mul_of_nonneg_left (hphase _ hwu).2 hh.le
      rw[hu,div_pow,Real.sq_sqrt hh.le] at ht
      exact ht.trans_eq (by field_simp)
    unfold compactCenteredFiniteModel
    rw[norm_div,norm_mul]
    apply (div_le_div_of_nonneg_right
      (mul_le_mul hex hsum (norm_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)).trans
    have hhalf:(0:ℝ)<1/2:=by norm_num
    have he:=div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos (‖w‖^2)).le (by positivity:0≤2*C)) hhalf hbase
    exact he.trans_eq (by ring)
end WP.Analysis
