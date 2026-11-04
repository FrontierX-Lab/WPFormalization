import WPFormalization.Analysis.GevreyOneInverse
import WPFormalization.Analysis.GevreyOneShift
import WPFormalization.HigherOrder.EndpointFormal
/-! Actual unit-series logarithms. The analytic logarithm's exact Taylor jets
are identified with the prescribed finiteLog by the proved formal derivative
identity. Uniform Cauchy bounds give pointwise actual-value errors and a full
linear-window real matching theorem, without a deferred asymptotic input. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open Filter PowerSeries
open scoped Topology

lemma derivative_logOf_mul_unit (P:PowerSeries ℂ)(hP:PowerSeries.constantCoeff P=1):
    PowerSeries.derivative (PowerSeries.logOf P)*P=PowerSeries.derivative P:=by
  have hQ:PowerSeries.constantCoeff (P-1)=0:=by simp only[map_sub,map_one,hP,sub_self]
  have hs:PowerSeries.HasSubst (P-1):=PowerSeries.HasSubst.of_constantCoeff_zero' hQ
  have hOne:(1:PowerSeries ℂ).subst (P-1)=1:=by
    rw[←PowerSeries.coe_substAlgHom hs,map_one]
  have hA:(1+PowerSeries.X:PowerSeries ℂ).subst (P-1)=P:=by
    rw[PowerSeries.subst_add hs,hOne,PowerSeries.subst_X hs]
    ring
  have hh:=congrArg (fun F:PowerSeries ℂ=>F.subst (P-1)) (PowerSeries.derivative_log_mul_one_add_X (A:=ℂ))
  rw[PowerSeries.subst_mul hs,hA,hOne] at hh
  rw[PowerSeries.logOf,PowerSeries.derivative_subst hs,map_sub,PowerSeries.derivative_one,sub_zero]
  calc
    _ = ((PowerSeries.derivative (PowerSeries.log ℂ)).subst (P-1)*P)*PowerSeries.derivative P:=by ring
    _ = _:=by rw[hh,one_mul]

lemma taylor_log_comp_unit (f:ℂ→ℂ)(hf:AnalyticAt ℂ f 0)(h0:f 0=1):
    taylor (fun z=>Complex.log (f z))=PowerSeries.logOf (taylor f):=by
  have hplane:f 0∈Complex.slitPlane:=by rw[h0];simp
  have hL:AnalyticAt ℂ (fun z=>Complex.log (f z)) 0:=(analyticAt_clog hplane).comp hf
  have hP0:PowerSeries.constantCoeff (taylor f)=1:=by rw[taylor_constant,h0]
  have hPne:taylor f≠0:=by intro he;have hh:=congrArg PowerSeries.constantCoeff he;rw[hP0,map_zero] at hh;exact one_ne_zero hh
  have hder:(fun z=>deriv (fun w=>Complex.log (f w)) z*f z)=ᶠ[𝓝 0] deriv f:=by
    filter_upwards [hf.eventually_analyticAt,hf.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds hplane)] with z hz hzp
    have hd:HasDerivAt (fun w=>Complex.log (f w)) ((f z)⁻¹*deriv f z) z:=
      (Complex.hasDerivAt_log hzp).comp z hz.differentiableAt.hasDerivAt
    rw[hd.deriv]
    have hn:f z≠0:=Complex.slitPlane_ne_zero hzp
    field_simp
  have he:=taylor_congr hder
  rw[taylor_mul hL.deriv hf,taylor_deriv,taylor_deriv] at he
  have hlog:=derivative_logOf_mul_unit (taylor f) hP0
  apply PowerSeries.derivative.ext
  · exact mul_right_cancel₀ hPne (he.trans hlog.symm)
  · rw[taylor_constant,h0,Complex.log_one,PowerSeries.constantCoeff_logOf hP0]

lemma logOf_coeff_finite (P:PowerSeries ℂ)(hP:PowerSeries.constantCoeff P=1)(n:ℕ):
    PowerSeries.coeff n (PowerSeries.logOf P)=
      ∑k∈Finset.Icc 1 n,(-1:ℂ)^(k+1)*PowerSeries.coeff n ((P-1)^k)/(k:ℂ):=by
  have hz:PowerSeries.constantCoeff (P-1)=0:=by simp only[map_sub,map_one,hP,sub_self]
  rw[PowerSeries.logOf,coeff_subst_finite _ _ hz]
  have hterm(k:ℕ):PowerSeries.coeff k (PowerSeries.log ℂ)*PowerSeries.coeff n ((P-1)^k)=
      (-1:ℂ)^(k+1)*PowerSeries.coeff n ((P-1)^k)/(k:ℂ):=by
    rw[PowerSeries.coeff_log]
    by_cases hk:k=0
    · subst k;simp
    · simp only[ite_eq_right hk,map_div₀,map_pow,map_neg,map_one,map_natCast]
      ring
  simp_rw[hterm]
  have he:Finset.range (n+1)=insert 0 (Finset.Icc 1 n):=by ext k;simp;omega
  rw[he,Finset.sum_insert (by simp)]
  simp

lemma truncatedSeriesPolynomial_log_coeff (f:WP.HigherOrder.Series)
    (hf0:PowerSeries.constantCoeff f=1)(K n:ℕ)(hn:n≤K):
    WP.coeff (fun z=>Complex.log (truncatedSeriesPolynomial f K z)) n=
      ((PowerSeries.coeff n (WP.HigherOrder.finiteLog f):ℝ):ℂ):=by
  have h0:truncatedSeriesPolynomial f K 0=1:=by
    have he:=truncatedSeriesPolynomial_coeff f K 0
    simpa only[WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,
      ite_eq_left (Nat.zero_le K),PowerSeries.coeff_zero_eq_constantCoeff,hf0,Complex.ofReal_one] using he
  rw[←taylor_coeff,taylor_log_comp_unit _ (truncatedSeriesPolynomial_analytic f K 0) h0,
    logOf_coeff_finite _ (by rw[taylor_constant,h0]),WP.HigherOrder.finiteLog,PowerSeries.coeff_mk]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hp:∀i≤K,PowerSeries.coeff i (taylor (truncatedSeriesPolynomial f K)-1)=
      PowerSeries.coeff i (PowerSeries.map Complex.ofRealHom (f-1)):=by
    intro i hi
    rw[map_sub,taylor_coeff,truncatedSeriesPolynomial_coeff,ite_eq_left hi,PowerSeries.coeff_map,map_sub]
    simp only[PowerSeries.coeff_one,Complex.ofReal_sub]
    split_ifs <;> norm_num
  rw[coeff_pow_eq_of_coeff_eq _ _ K hp k n hn,←map_pow,PowerSeries.coeff_map]
  rfl


lemma slitPlane_of_norm_sub_one_half (w:ℂ)(hw:‖w-1‖≤1/2):w∈Complex.slitPlane:=by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have he:|w.re-1|≤1/2:=by
    simpa only[Complex.sub_re,Complex.one_re] using (Complex.abs_re_le_norm (w-1)).trans hw
  linarith[(abs_le.mp he).1]

lemma log_truncated_polynomial_remainder (f:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf0:PowerSeries.constantCoeff f=1)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(z:ℂ)(hz:‖z‖≤1/(16*(C+1)*B*((K:ℝ)+1))):
    ‖Complex.log (truncatedSeriesPolynomial f K z)-
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.finiteLog f):ℝ):ℂ)*z^i‖≤
      2*(8*(C+1)*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)*‖z‖^(K+1):=by
  let B':ℝ:=4*(C+1)*B
  have hBp:0<B':=by dsimp[B'];positivity
  have hdata(w:ℂ)(hw:‖w‖≤1/(2*B'*((K:ℝ)+1))):
      truncatedSeriesPolynomial f K w∈Complex.slitPlane ∧ ‖Complex.log (truncatedSeriesPolynomial f K w)‖≤1:=by
    have hs:‖truncatedSeriesPolynomial f K w-1‖≤1/2:=
      (truncatedSeriesPolynomial_unit_data f C B hC hB hf0 hf K w
        (by convert hw using 1;dsimp[B'];ring)).1
    refine ⟨slitPlane_of_norm_sub_one_half _ hs,?_⟩
    have he:=Complex.norm_log_one_add_half_le_self hs
    rw[show (1:ℂ)+(truncatedSeriesPolynomial f K w-1)=truncatedSeriesPolynomial f K w by ring] at he
    nlinarith
  have hd:DifferentiableOn ℂ (fun w=>Complex.log (truncatedSeriesPolynomial f K w))
      (Metric.closedBall 0 (1/(2*B'*((K:ℝ)+1)))):=by
    intro w hw
    have hw':‖w‖≤1/(2*B'*((K:ℝ)+1)):=by simpa only[Metric.mem_closedBall,dist_zero_right] using hw
    exact ((analyticAt_clog (hdata w hw').1).comp
      (truncatedSeriesPolynomial_analytic f K w)).differentiableAt.differentiableWithinAt
  have hc:∀w∈Metric.sphere (0:ℂ) (1/(2*B'*((K:ℝ)+1))),‖Complex.log (truncatedSeriesPolynomial f K w)‖≤1:=by
    intro w hw
    exact (hdata w (by simpa only[Metric.mem_closedBall,dist_zero_right] using Metric.sphere_subset_closedBall hw)).2
  have hz':‖z‖≤1/(4*B'*((K:ℝ)+1)):=by convert hz using 1;dsimp[B'];ring
  have he:=complex_taylor_linear_factorial_bound (fun w=>Complex.log (truncatedSeriesPolynomial f K w))
    B' 1 hBp (by norm_num) K hd hc z hz'
  have hcoef:(∑i∈Finset.range (K+1),WP.coeff (fun w=>Complex.log (truncatedSeriesPolynomial f K w)) i*z^i)=
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.finiteLog f):ℝ):ℂ)*z^i:=by
    apply Finset.sum_congr rfl
    intro i hi
    rw[truncatedSeriesPolynomial_log_coeff f hf0 K i (by have hh:=Finset.mem_range.mp hi;omega)]
  rw[hcoef] at he
  convert he using 1;dsimp[B'];ring

lemma log_abs_sub_le_of_half_lower (x y:ℝ)(hx:1/2≤x)(hy:1/2≤y):
    |Real.log x-Real.log y|≤2*|x-y|:=by
  have hb:∀t∈Set.Ici (1/2:ℝ),‖deriv Real.log t‖≤2:=by
    intro t ht
    have ht0:0<t:=lt_of_lt_of_le (by norm_num) ht
    rw[Real.deriv_log,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht0),←one_div]
    apply (div_le_iff₀ ht0).mpr
    have ht' : (1/2:ℝ)≤t:=ht
    linarith
  have he:=Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (ht:t∈Set.Ici (1/2:ℝ))=>Real.differentiableAt_log (ne_of_gt (lt_of_lt_of_le (by norm_num) ht)))
    hb (convex_Ici (1/2:ℝ)) (show y∈Set.Ici (1/2:ℝ) from hy) (show x∈Set.Ici (1/2:ℝ) from hx)
  simpa only[Real.norm_eq_abs] using he


lemma log_truncated_polynomial_real_remainder (f:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf0:PowerSeries.constantCoeff f=1)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(h:ℝ)(hh:0<h)(hw:16*(C+1)*B*((K:ℝ)+1)≤h):
    |Real.log (inversePowerTruncation f K h)-inversePowerTruncation (WP.HigherOrder.finiteLog f) K h|≤
      2*(8*(C+1)*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(16*(C+1)*B*((K:ℝ)+1)):=by
    rw[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
    exact one_div_le_one_div_of_le (by positivity) hw
  have he:=log_truncated_polynomial_remainder f C B hC hB hf0 hf K ((1/h:ℝ):ℂ) hz
  have hp(s:WP.HigherOrder.Series):truncatedSeriesPolynomial s K ((1/h:ℝ):ℂ)=
      ((inversePowerTruncation s K h):ℂ):=by
    rw[truncatedSeriesPolynomial_real]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw[div_pow,one_pow,mul_one_div]
  have hq:(∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.finiteLog f):ℝ):ℂ)*((1/h:ℝ):ℂ)^i)=
      ((inversePowerTruncation (WP.HigherOrder.finiteLog f) K h):ℂ):=by
    change truncatedSeriesPolynomial (WP.HigherOrder.finiteLog f) K ((1/h:ℝ):ℂ)=_
    exact hp _
  have hr:=(Complex.abs_re_le_norm _).trans he
  rw[hp,hq,Complex.sub_re,Complex.log_ofReal_re,Complex.ofReal_re] at hr
  simp only[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh),div_pow,one_pow] at hr
  convert hr using 1;ring

lemma log_value_truncation_error (f:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf0:PowerSeries.constantCoeff f=1)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(h:ℝ)(hh:0<h)(hw:16*(C+1)*B*((K:ℝ)+1)≤h)
    (x E:ℝ)(hx0:|x-1|≤1/2)(hx:|x-inversePowerTruncation f K h|≤E):
    |Real.log x-inversePowerTruncation (WP.HigherOrder.finiteLog f) K h|≤2*E+
      2*(8*(C+1)*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(8*(C+1)*B*((K:ℝ)+1)):=by
    rw[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
    apply one_div_le_one_div_of_le (by positivity)
    have hK:0<(K:ℝ)+1:=by positivity
    nlinarith[mul_nonneg (by positivity:0≤(C+1)*B) hK.le]
  have hdata:=truncatedSeriesPolynomial_unit_data f C B hC hB hf0 hf K ((1/h:ℝ):ℂ) hz
  have hp:truncatedSeriesPolynomial f K ((1/h:ℝ):ℂ)=((inversePowerTruncation f K h):ℂ):=by
    rw[truncatedSeriesPolynomial_real]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw[div_pow,one_pow,mul_one_div]
  rw[hp,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hdata
  have hP0:|inversePowerTruncation f K h-1|≤1/2:=hdata.1
  have hxlow:1/2≤x:=by linarith[(abs_le.mp hx0).1]
  have hPlow : (1/2:ℝ) ≤ inversePowerTruncation f K h :=by linarith[(abs_le.mp hP0).1]
  have hdiff:|Real.log x-Real.log (inversePowerTruncation f K h)|≤2*E:=
    (log_abs_sub_le_of_half_lower _ _ hxlow hPlow).trans (mul_le_mul_of_nonneg_left hx (by norm_num))
  exact (abs_sub_le _ _ _).trans (add_le_add hdiff
    (log_truncated_polynomial_real_remainder f C B hC hB hf0 hf K h hh hw))

lemma GevreyOneAsymptotic.log_unit (F:ℝ→ℝ)(f:WP.HigherOrder.Series)
    (hF:GevreyOneAsymptotic F f)(hf0:PowerSeries.constantCoeff f=1):
    GevreyOneAsymptotic (fun h=>Real.log (F h)) (WP.HigherOrder.finiteLog f):=by
  obtain ⟨C₀,B₀,hC₀,hB₀,hcoeff⟩:=GevreyOneAsymptotic.coeff_bound F f hF
  obtain ⟨C₁,B₁,q,H₀,hC₁,hB₁,hq,hH₀,herr⟩:=hF
  let T:ℝ:=(C₀+1)*B₀
  have hT:0<T:=by dsimp[T];positivity
  let q':ℝ:=min q (1/(32*T))
  let H:ℝ:=max H₀ (max (32*T) (2*C₁*B₁+1))
  let B:ℝ:=B₁+8*T*Real.exp 1
  let C:ℝ:=2*C₁+2
  refine ⟨C,B,q',H,by dsimp[C];positivity,by dsimp[B];positivity,
    lt_min hq (by positivity),lt_of_lt_of_le hH₀ (le_max_left _ _),?_⟩
  intro K h hhH hK
  have hh₀:H₀≤h:=(le_max_left _ _).trans hhH
  have hhT:32*T≤h:=((le_max_left _ _).trans (le_max_right _ _)).trans hhH
  have hhC:2*C₁*B₁+1≤h:=((le_max_right _ _).trans (le_max_right _ _)).trans hhH
  have hh:0<h:=lt_of_lt_of_le hH₀ hh₀
  have hKq:(K:ℝ)≤q*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hh.le)
  have hKr:(K:ℝ)≤(1/(32*T))*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hh.le)
  have hwindow:16*T*((K:ℝ)+1)≤h:=by
    have hk':(K:ℝ)*(32*T)≤h := (le_div_iff₀ (by positivity:0<32*T)).mp
      (by simpa only[one_div,mul_comm,div_eq_mul_inv,one_mul] using hKr)
    nlinarith
  have hx0:|F h-1|≤1/2:=by
    have he:=herr 0 h hh₀ (by have hpos:=mul_pos hq hh;simpa only[Nat.cast_zero] using hpos.le)
    simp only[inversePowerTruncation,Finset.sum_range_one,pow_zero,div_one,Nat.zero_add,pow_one,
      Nat.factorial_one,Nat.cast_one,mul_one,PowerSeries.coeff_zero_eq_constantCoeff,hf0] at he
    apply he.trans
    apply (div_le_iff₀ hh).mpr
    linarith
  have he:=log_value_truncation_error f C₀ B₀ hC₀.le hB₀ hf0 hcoeff K h hh (by simpa only[T,mul_assoc] using hwindow)
    (F h) (C₁*B₁^(K+1)*((K+1).factorial:ℝ)/h^(K+1)) hx0 (herr K h hh₀ hKq)
  have hb₁:B₁≤B:=le_add_of_nonneg_right (by positivity)
  have hb₂:8*T*Real.exp 1≤B:=le_add_of_nonneg_left hB₁.le
  calc
    _ ≤ 2*(C₁*B₁^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        2*(8*T*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by simpa only[T,mul_assoc] using he
    _ ≤ 2*(C₁*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        2*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by gcongr
    _ = _:=by dsimp[C];ring

end WP.Analysis
