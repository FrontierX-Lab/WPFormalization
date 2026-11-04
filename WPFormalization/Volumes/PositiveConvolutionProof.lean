import WPFormalization.Intersection.PositiveKernelPolynomial
import WPFormalization.Volumes.PlanarInverse
import WPFormalization.Statements.ConvolutionDefinitions
/-! The actual positive convolution factor, Lemma 9.1.
Finite positive homogeneous kernel polynomials, actual planar inverse
continuation, positive analytic composition and the original Phi quotient
are all instantiated. The full complex disk Taylor convergence is proved;
no convolution or coefficient positivity assumption is introduced. -/
noncomputable section
namespace WP.PositiveConvolution
open Set Filter
open scoped Topology
lemma kernel_inverse_positiveJets (l:ℕ):PositiveJets (Analysis.kInverseCoeff l):=by
  apply PositiveJets.of_coefficients
  · intro n
    simpa only[Analysis.realTaylor_coeff] using Analysis.K_kernel_parameter_nonneg.2 n l
  · exact Analysis.kInverseCoeff_parameter_real l
lemma kernel_inverse_ofReal (l:ℕ) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀):
    Analysis.kInverseCoeff l (Y:ℂ)=Complex.ofReal ((Analysis.kInverseCoeff l (Y:ℂ)).re):=by
  have hn:‖(Y:ℂ)‖<y₀:=by simpa only[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hY.1] using hY.2
  have hs:=Analysis.kInverseCoeff_hasSum l (Y:ℂ) hn
  have hterm(n:ℕ):(WP.coeff (Analysis.kInverseCoeff l) n*(Y:ℂ)^n).im=0:=by
    rw[←Complex.ofReal_pow]
    simp only[Complex.mul_im,Analysis.kInverseCoeff_parameter_real l n,Complex.ofReal_im,
      mul_zero,zero_mul,add_zero]
  have hi:=Complex.imCLM.hasSum hs
  change HasSum (fun n=>(WP.coeff (Analysis.kInverseCoeff l) n*(Y:ℂ)^n).im)
    (Analysis.kInverseCoeff l (Y:ℂ)).im at hi
  have hz:HasSum (fun _:ℕ=>(0:ℝ)) (Analysis.kInverseCoeff l (Y:ℂ)).im:=by simpa only[hterm] using hi
  apply Complex.ext
  · rfl
  · simpa only[Complex.ofReal_im] using (hasSum_zero.unique hz).symm
lemma polynomial_eval_ofReal (F:KernelPolynomial) (v:ℕ→ℝ):
    MvPolynomial.eval₂ nnComplexHom (fun l=>Complex.ofReal (v l)) F=Complex.ofReal (evalKernel v F):=by
  change MvPolynomial.eval₂ nnComplexHom _ F=Complex.ofReal (MvPolynomial.eval₂ NNReal.toRealHom v F)
  simp only[MvPolynomial.eval₂_eq]
  simp only[Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_pow]
  rfl
lemma polynomial_analyticAt_point (F:KernelPolynomial) (v:ℕ→ℂ→ℂ) (x:ℂ)
    (hf:∀l,AnalyticAt ℂ (v l) x):
    AnalyticAt ℂ (fun z=>MvPolynomial.eval₂ nnComplexHom (fun l=>v l z) F) x:=by
  classical
  change AnalyticAt ℂ (fun z=>∑d∈F.support,nnComplexHom (F.coeff d)*∏l∈d.support,(v l z)^(d l)) x
  apply Finset.analyticAt_fun_sum
  intro d hd
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro l hl
  exact (hf l).pow _
def regularizedKernelPolynomial (P:PsiTheory) (F:KernelPolynomial) (z:ℂ):ℂ:=
  MvPolynomial.eval₂ nnComplexHom (fun l=>Analysis.kInverseCoeff l (planarInverse P z)) F
lemma regularizedKernelPolynomial_analyticAt (P:PsiTheory) (F:KernelPolynomial)
    (z:ℂ) (hz:‖z‖<xCritical):AnalyticAt ℂ (regularizedKernelPolynomial P F) z:=by
  apply polynomial_analyticAt_point
  intro l
  exact (Analysis.kInverseCoeff_analyticAt l _ (derivX_planarInverse_ne_zero P z hz)).comp
    (planarInverse_analyticAt P z hz)
lemma regularizedKernelPolynomial_positiveJets (P:PsiTheory) (F:KernelPolynomial):
    PositiveJets (regularizedKernelPolynomial P F):=by
  have hzero:‖(0:ℂ)‖<xCritical:=by simpa only[norm_zero] using Analysis.xCritical_pos_parameter
  have ha:deriv X (0:ℂ)≠0:=by rw[Analysis.derivX_zero];exact one_ne_zero
  apply polynomial_positiveJets
  · intro l
    exact (Analysis.kInverseCoeff_analyticAt l _ (derivX_planarInverse_ne_zero P 0 hzero)).comp
      (planarInverse_analyticAt P 0 hzero)
  · intro l
    exact PositiveJets.comp (Analysis.kInverseCoeff_analyticAt l 0 ha) (planarInverse_analyticAt P 0 hzero)
      (planarInverse_zero P) (kernel_inverse_positiveJets l) (planarInverse_positiveJets P)
lemma Phi_iteratedDeriv_ofReal (P:PsiTheory) (g p:ℕ) (hs:Stable g p)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    iteratedDeriv p (Phi P g) (x:ℂ)=Complex.ofReal (shifted P g (List.replicate p 0) (inverseY x)):=by
  have hy:=inverseY_branch x hx
  have hv:=string_flow_proof P g p hs (inverseY x) hy.1
  rw[hy.2] at hv
  apply Complex.ext
  · simpa only[Complex.ofReal_re,markedF] using hv.symm
  · simpa only[Complex.ofReal_im] using Phi_iteratedDeriv_real P g p x
      (by simpa only[abs_of_nonneg hx.1] using hx.2)
lemma factorization_by_positive_polynomial (P:PsiTheory) (g p:ℕ) (hp:1 ≤ p) (hs:Stable g p):
    ∃F:KernelPolynomial,∀z:ℂ,‖z‖<xCritical→
      iteratedDeriv p (Phi P g) z=iteratedDeriv 3 (Phi P 0) z^(complexity g p)*regularizedKernelPolynomial P F z:=by
  obtain ⟨F,hGrade,hEval⟩:=exists_regularized_amplitude_polynomial P g (List.replicate p 0)
    (by simpa only[List.length_replicate] using hp) (by simpa only[List.length_replicate] using hs) (by simp)
  refine ⟨F,?_⟩
  let f:ℂ→ℂ:=iteratedDeriv p (Phi P g)
  let q:ℂ→ℂ:=fun z=>iteratedDeriv 3 (Phi P 0) z^(complexity g p)*regularizedKernelPolynomial P F z
  have hf:AnalyticOnNhd ℂ f (Metric.ball 0 xCritical):=by
    intro z hz
    have hz':‖z‖<xCritical:=by simpa only[Metric.mem_ball,dist_zero_right] using hz
    simpa only[f,iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P g z hz').iterated_deriv p
  have hq:AnalyticOnNhd ℂ q (Metric.ball 0 xCritical):=by
    intro z hz
    have hz':‖z‖<xCritical:=by simpa only[Metric.mem_ball,dist_zero_right] using hz
    have hv:AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) z:=by
      simpa only[iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P 0 z hz').iterated_deriv 3
    exact (hv.pow _).mul (regularizedKernelPolynomial_analyticAt P F z hz')
  have hxc:=Analysis.xCritical_pos_parameter
  have hc:xCritical/2∈Ioo (0:ℝ) xCritical:=⟨half_pos hxc,half_lt_self hxc⟩
  have hmem:((xCritical/2:ℝ):ℂ)∈Metric.ball 0 xCritical:=by
    simpa only[Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc.1] using hc.2
  have he:EqOn f q (Metric.ball 0 xCritical):=by
    apply Analysis.complex_identity_of_real_germ f q _ (xCritical/2) hf hq
      (convex_ball (0:ℂ) xCritical).isPreconnected hmem
    filter_upwards[isOpen_Ioo.mem_nhds hc] with x hx
    have hx':x∈Ico (0:ℝ) xCritical:=⟨hx.1.le,hx.2⟩
    have hy:=inverseY_branch x hx'
    have hPoly:regularizedKernelPolynomial P F (x:ℂ)=
        Complex.ofReal (a (inverseY x)^(complexity g p)*shifted P g (List.replicate p 0) (inverseY x)):=by
      unfold regularizedKernelPolynomial
      rw[planarInverse_ofReal P x hx']
      have hfun:(fun l=>Analysis.kInverseCoeff l (Complex.ofReal (inverseY x)))=
          fun l=>Complex.ofReal (Analysis.kInverseCoeff l (Complex.ofReal (inverseY x))).re:=by
        funext l
        exact kernel_inverse_ofReal l (inverseY x) hy.1
      rw[hfun,polynomial_eval_ofReal]
      have hv:=hEval (inverseY x) hy.1
      simpa only[List.length_replicate] using congrArg Complex.ofReal hv.symm
    dsimp[f,q]
    rw[Phi_iteratedDeriv_ofReal P g p hs x hx',planarThird_ofReal P x hx',hPoly]
    rw[←Complex.ofReal_pow,←Complex.ofReal_mul]
    congr 1
    have hA:a (inverseY x)≠0:=(a_pos _ hy.1).ne'
    rw[inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hA),one_mul]
  intro z hz
  exact he (by simpa only[Metric.mem_ball,dist_zero_right] using hz)
end WP.PositiveConvolution
namespace WP
open PositiveConvolution Filter
open scoped Topology
lemma positive_convolution_proof (P:PsiTheory) (g p:ℕ) (hp:1 ≤ p) (hst:Stable g p):
    (∀x∈Set.Ico 0 xCritical,universalV P x=Complex.ofReal ((a (inverseY x))⁻¹) ∧
      iteratedDeriv p (Phi P g) x=universalV P x^(complexity g p)*convolutionR P g p x) ∧
    (∀j,0 ≤ realCoeff (convolutionR P g p) j) ∧
    (∀z:ℂ,‖z‖<xCritical→HasSum (fun j=>coeff (convolutionR P g p) j*z^j) (convolutionR P g p z)):=by
  obtain ⟨F,hFactor⟩:=factorization_by_positive_polynomial P g p hp hst
  have hV(z:ℂ)(hz:‖z‖<xCritical):universalV P z≠0:=planar_third_ne_zero P z hz
  have hR(z:ℂ)(hz:‖z‖<xCritical):convolutionR P g p z=regularizedKernelPolynomial P F z:=by
    unfold convolutionR universalV
    rw[hFactor z hz]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (hV z hz))
  have hRanalytic(z:ℂ)(hz:‖z‖<xCritical):AnalyticAt ℂ (convolutionR P g p) z:=by
    have hf:AnalyticAt ℂ (iteratedDeriv p (Phi P g)) z:=by
      simpa only[iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P g z hz).iterated_deriv p
    have hv:AnalyticAt ℂ (universalV P) z:=by
      change AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) z
      simpa only[iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P 0 z hz).iterated_deriv 3
    exact hf.div (hv.pow _) (pow_ne_zero _ (hV z hz))
  refine ⟨?_,?_,?_⟩
  · intro x hx
    refine ⟨planarThird_ofReal P x hx,?_⟩
    have hz:‖(x:ℂ)‖<xCritical:=by simpa only[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
    rw[hR (x:ℂ) hz]
    exact hFactor (x:ℂ) hz
  · have he:(convolutionR P g p)=ᶠ[𝓝 (0:ℂ)] regularizedKernelPolynomial P F:=by
      filter_upwards[Metric.ball_mem_nhds (0:ℂ) Analysis.xCritical_pos_parameter] with z hz
      exact hR z (by simpa only[Metric.mem_ball,dist_zero_right] using hz)
    intro j
    have hc:coeff (convolutionR P g p) j=coeff (regularizedKernelPolynomial P F) j:=by
      unfold coeff
      rw[he.iteratedDeriv_eq]
    have hb:=(regularizedKernelPolynomial_positiveJets P F).coefficient_nonneg j
    simpa only[realCoeff,hc] using hb.1
  · intro z hz
    exact analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter hRanalytic z hz
end WP
