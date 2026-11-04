import WPFormalization.Analysis.PositiveAnalyticJets
import WPFormalization.Volumes.StringFlowProof
import WPFormalization.Analysis.ComplexGermGluing
/-! The genuine planar inverse is the second derivative of Phi_0 on the
complete cusp disk. Its Taylor jets are nonnegative by the actual EGF.
The string-flow initial value and parameter derivative identify the real
inverse, and the identity principle gives X'(Y_c) times the third Phi_0
 derivative equal to one throughout the disk. Both factors are nonzero.
No inverse coefficient or convolution hypothesis is used. -/
noncomputable section
namespace WP.PositiveConvolution
open Set Filter
open scoped Topology
lemma Phi_iteratedDeriv_zero (P:PsiTheory) (g n:ℕ):
    iteratedDeriv n (Phi P g) 0=(shifted P g (List.replicate n 0) 0:ℂ):=by
  rw[Phi_eq_shifted_scalar_series]
  exact Analysis.scalar_series_iteratedDeriv_zero _
    ((ENNReal.ofReal_pos.mpr Analysis.xCritical_pos_parameter).trans_le (shifted_scalar_series_radius P g)) n
lemma analytic_ball_hasSum (f:ℂ→ℂ) (R:ℝ) (hR:0<R)
    (hf:∀z:ℂ,‖z‖<R→AnalyticAt ℂ f z) (z:ℂ) (hz:‖z‖<R):
    HasSum (fun n=>WP.coeff f n*z^n) (f z):=by
  have hd:DifferentiableOn ℂ f (Metric.ball 0 R):=by
    intro w hw
    exact (hf w (by simpa only[Metric.mem_ball,dist_zero_right] using hw)).differentiableAt.differentiableWithinAt
  have hs:=Complex.hasSum_taylorSeries_on_ball hd (by simpa only[Metric.mem_ball,dist_zero_right] using hz)
  convert hs using 1
  ext n
  simp only[WP.coeff,sub_zero,smul_eq_mul]
  ring
lemma Phi_iteratedDeriv_real (P:PsiTheory) (g p:ℕ) (x:ℝ) (hx:|x|<xCritical):
    (iteratedDeriv p (Phi P g) (x:ℂ)).im=0:=by
  have ha (z:ℂ) (hz:‖z‖<xCritical):AnalyticAt ℂ (iteratedDeriv p (Phi P g)) z:=
    by simpa only[iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P g z hz).iterated_deriv p
  have hs:=analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter ha (x:ℂ)
    (by simpa only[Complex.norm_real,Real.norm_eq_abs] using hx)
  have hterm (n:ℕ):(WP.coeff (iteratedDeriv p (Phi P g)) n*(x:ℂ)^n).im=0:=by
    unfold WP.coeff
    rw[Analysis.iteratedDeriv_iteratedDeriv_eq,Phi_iteratedDeriv_zero]
    rw[←Complex.ofReal_pow]
    simp only[Complex.mul_im,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.natCast_re,Complex.natCast_im,mul_zero,zero_mul,sub_zero,zero_div,add_zero]
  have hz:HasSum (fun _:ℕ=>(0:ℝ)) ((iteratedDeriv p (Phi P g) (x:ℂ)).im):=by
    have hi:=Complex.imCLM.hasSum hs
    change HasSum (fun n=>(WP.coeff (iteratedDeriv p (Phi P g)) n*(x:ℂ)^n).im)
      ((iteratedDeriv p (Phi P g) (x:ℂ)).im) at hi
    simpa only[hterm] using hi
  exact (hasSum_zero.unique hz).symm

def planarInverse (P:PsiTheory) (z:ℂ):ℂ:=iteratedDeriv 2 (Phi P 0) z
lemma planarInverse_analyticAt (P:PsiTheory) (z:ℂ) (hz:‖z‖<xCritical):
    AnalyticAt ℂ (planarInverse P) z:=by
  change AnalyticAt ℂ (iteratedDeriv 2 (Phi P 0)) z
  simpa only[iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P 0 z hz).iterated_deriv 2
lemma planarInverse_zero (P:PsiTheory):planarInverse P 0=0:=by
  rw[planarInverse,Phi_iteratedDeriv_zero]
  norm_num[shifted,Stable]
lemma planarInverse_positiveJets (P:PsiTheory):PositiveJets (planarInverse P):=by
  intro n
  have hn:0 ≤ shifted P 0 (List.replicate (n+2) 0) 0:=
    shifted_zero_nonneg_nonempty P 0 (n+2) (by omega) 0 ⟨le_rfl,y₀_pos⟩
  refine ⟨⟨_,hn⟩,?_⟩
  change iteratedDeriv n (iteratedDeriv 2 (Phi P 0)) 0=_
  rw[Analysis.iteratedDeriv_iteratedDeriv_eq,Phi_iteratedDeriv_zero]
  rfl
lemma shifted_planar_three (P:PsiTheory) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀):
    shifted P 0 (List.replicate 3 0) Y=(a Y)⁻¹:=by
  have hb:=(initial_amplitudes P Y ⟨hY.1,hY.2.le⟩).1
  rw[normalized,ite_eq_right (ne_of_lt hY.2)] at hb
  norm_num[complexity,deficit,dimension] at hb
  have ha:a Y≠0:=(a_pos Y hY).ne'
  apply (mul_left_cancel₀ ha)
  simpa only[List.replicate_succ,List.replicate_zero,mul_inv_cancel₀ ha] using hb
lemma marked_planar_third (P:PsiTheory) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀):
    markedF P 0 3 (XR Y)=(a Y)⁻¹:=by
  rw[←string_flow_proof P 0 3 (by norm_num[Stable]) Y hY]
  exact shifted_planar_three P Y hY
lemma planar_second_parameter_deriv (P:PsiTheory) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀):
    HasDerivAt (fun t:ℝ=>markedF P 0 2 (XR t)) 1 Y:=by
  have hd:=markedF_parameter_hasDerivAt P 0 2 Y hY
  rw[marked_planar_third P Y hY,mul_inv_cancel₀ (a_pos Y hY).ne'] at hd
  exact hd
lemma planar_second_parameter_value (P:PsiTheory) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀):
    markedF P 0 2 (XR Y)=Y:=by
  have hderiv (t:ℝ) (ht:t∈Set.uIcc (0:ℝ) Y):
      HasDerivAt (fun s:ℝ=>markedF P 0 2 (XR s)) 1 t:=by
    rw[Set.uIcc_of_le hY.1] at ht
    exact planar_second_parameter_deriv P t ⟨ht.1,ht.2.trans_lt hY.2⟩
  have hf:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=Y) hderiv intervalIntegrable_const
  have hzero:markedF P 0 2 (XR 0)=0:=by
    rw[XR_zero]
    change (planarInverse P 0).re=0
    rw[planarInverse_zero,Complex.zero_re]
  rw[hzero,sub_zero,intervalIntegral.integral_const,smul_eq_mul,mul_one,sub_zero] at hf
  exact hf.symm
end WP.PositiveConvolution

namespace WP.PositiveConvolution
open Set Filter
open scoped Topology
lemma planarInverse_ofReal (P:PsiTheory) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    planarInverse P (x:ℂ)=Complex.ofReal (inverseY x):=by
  have hy:=inverseY_branch x hx
  have hv:=planar_second_parameter_value P (inverseY x) hy.1
  rw[hy.2] at hv
  apply Complex.ext
  · simpa only[Complex.ofReal_re,markedF,planarInverse] using hv
  · simpa only[planarInverse,Complex.ofReal_im] using Phi_iteratedDeriv_real P 0 2 x
      (by simpa only[abs_of_nonneg hx.1] using hx.2)
lemma planarThird_ofReal (P:PsiTheory) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    iteratedDeriv 3 (Phi P 0) (x:ℂ)=Complex.ofReal ((a (inverseY x))⁻¹):=by
  have hy:=inverseY_branch x hx
  have hv:=marked_planar_third P (inverseY x) hy.1
  rw[hy.2] at hv
  apply Complex.ext
  · simpa only[Complex.ofReal_re,markedF] using hv
  · simpa only[Complex.ofReal_im] using Phi_iteratedDeriv_real P 0 3 x
      (by simpa only[abs_of_nonneg hx.1] using hx.2)
lemma planar_inverse_derivative_identity (P:PsiTheory):
    ∀z:ℂ,‖z‖<xCritical→
      deriv X (planarInverse P z)*iteratedDeriv 3 (Phi P 0) z=1:=by
  have hxc:=Analysis.xCritical_pos_parameter
  let f:ℂ→ℂ:=fun z=>deriv X (planarInverse P z)*iteratedDeriv 3 (Phi P 0) z
  have hf:AnalyticOnNhd ℂ f (Metric.ball 0 xCritical):=by
    intro z hz
    have hn:‖z‖<xCritical:=by simpa only[Metric.mem_ball,dist_zero_right] using hz
    apply AnalyticAt.mul
    · exact ((X_differentiable.analyticAt _).deriv).comp (planarInverse_analyticAt P z hn)
    · simpa only[iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P 0 z hn).iterated_deriv 3
  have hc:xCritical/2∈Ioo (0:ℝ) xCritical:=⟨half_pos hxc,half_lt_self hxc⟩
  have hmem:((xCritical/2:ℝ):ℂ)∈Metric.ball 0 xCritical:=by
    simpa only[Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc.1] using hc.2
  have he:EqOn f (fun _:ℂ=>1) (Metric.ball 0 xCritical):=by
    apply Analysis.complex_identity_of_real_germ f (fun _:ℂ=>1) (Metric.ball 0 xCritical)
      (xCritical/2) hf analyticOnNhd_const (convex_ball (0:ℂ) xCritical).isPreconnected hmem
    filter_upwards[isOpen_Ioo.mem_nhds hc] with x hx
    have hx':x∈Ico (0:ℝ) xCritical:=⟨hx.1.le,hx.2⟩
    dsimp[f]
    rw[planarInverse_ofReal P x hx',planarThird_ofReal P x hx',derivX_ofReal]
    rw[←Complex.ofReal_mul,mul_inv_cancel₀ (a_pos _ (inverseY_branch x hx').1).ne',Complex.ofReal_one]
  intro z hz
  exact he (by simpa only[Metric.mem_ball,dist_zero_right] using hz)
lemma planar_third_ne_zero (P:PsiTheory) (z:ℂ) (hz:‖z‖<xCritical):
    iteratedDeriv 3 (Phi P 0) z≠0:=by
  intro hzero
  have hh:=planar_inverse_derivative_identity P z hz
  rw[hzero,mul_zero] at hh
  exact zero_ne_one hh
lemma derivX_planarInverse_ne_zero (P:PsiTheory) (z:ℂ) (hz:‖z‖<xCritical):
    deriv X (planarInverse P z)≠0:=by
  intro hzero
  have hh:=planar_inverse_derivative_identity P z hz
  rw[hzero,zero_mul] at hh
  exact zero_ne_one hh
end WP.PositiveConvolution
