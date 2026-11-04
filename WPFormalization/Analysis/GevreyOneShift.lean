import WPFormalization.Analysis.GevreyOneMatching
/-! Exact finite Taylor and actual matching under a fixed inverse-complexity shift. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open PowerSeries Filter
open scoped Topology

def inverseComplexShift (c:ℝ) (z:ℂ):ℂ:=z*(1-(c:ℂ)*z)⁻¹

lemma inverseComplexShift_analytic (c:ℝ) (z:ℂ) (hz:1-(c:ℂ)*z≠0):
    AnalyticAt ℂ (inverseComplexShift c) z := by
  unfold inverseComplexShift
  exact analyticAt_id.mul ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).inv hz)

lemma inverseComplexShift_zero (c:ℝ):inverseComplexShift c 0=0:=by simp[inverseComplexShift]

lemma inverseComplexShift_taylor (c:ℝ):
    taylor (inverseComplexShift c)=PowerSeries.X*(1-PowerSeries.C (c:ℂ)*PowerSeries.X)⁻¹ := by
  have hd:AnalyticAt ℂ (fun z:ℂ=>1-(c:ℂ)*z) 0:=by fun_prop
  have h0:(fun z:ℂ=>1-(c:ℂ)*z) 0≠0:=by simp
  have he:taylor (fun z:ℂ=>1-(c:ℂ)*z)=1-PowerSeries.C (c:ℂ)*PowerSeries.X:=by
    rw[taylor_sub (f:=fun _:ℂ=>1) (g:=fun z:ℂ=>(c:ℂ)*z) analyticAt_const (analyticAt_const.mul analyticAt_id),taylor_const_mul,taylor_id,taylor_const]
    simp
  change taylor (fun z:ℂ=>z*(1-(c:ℂ)*z)⁻¹)=_
  rw[taylor_mul (f:=fun z:ℂ=>z) (g:=fun z:ℂ=>(1-(c:ℂ)*z)⁻¹) analyticAt_id (hd.inv h0),taylor_id,taylor_inv hd h0,he]

lemma coeff_subst_finite (F P:PowerSeries ℂ) (hP:PowerSeries.constantCoeff P=0) (n:ℕ):
    PowerSeries.coeff n (F.subst P)=∑k∈Finset.range (n+1),PowerSeries.coeff k F*PowerSeries.coeff n (P^k) := by
  have hz(k:ℕ)(hnk:n<k):PowerSeries.coeff n (P^k)=0:=by
    obtain ⟨Q,hQ⟩:=PowerSeries.X_dvd_iff.mpr hP
    rw[hQ,mul_pow,PowerSeries.coeff_X_pow_mul',ite_eq_right (by omega)]
  have hs:Function.support (fun k:ℕ=>PowerSeries.coeff k F • PowerSeries.coeff n (P^k))⊆
      (Finset.range (n+1):Set ℕ):=by
    intro k hk
    by_contra hn
    have hnk:n<k:=by
      have hh:¬k<n+1:=by simpa only[Finset.mem_coe,Finset.mem_range] using hn
      omega
    exact hk (by dsimp only;rw[hz k hnk,smul_zero])
  rw[PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hP),finsum_eq_sum_of_support_subset _ hs]
  rfl

lemma truncatedSeriesPolynomial_comp_coeff (f:WP.HigherOrder.Series) (g:ℂ→ℂ)
    (hg:AnalyticAt ℂ g 0)(hg0:g 0=0)(K n:ℕ)(hn:n≤K):
    WP.coeff (fun z=>truncatedSeriesPolynomial f K (g z)) n=
      PowerSeries.coeff n ((PowerSeries.map Complex.ofRealHom f).subst (taylor g)) := by
  have hP:PowerSeries.constantCoeff (taylor g)=0:=by rw[taylor_constant,hg0]
  have hz(k:ℕ)(hnk:n<k):PowerSeries.coeff n ((taylor g)^k)=0:=by
    obtain ⟨Q,hQ⟩:=PowerSeries.X_dvd_iff.mpr hP
    rw[hQ,mul_pow,PowerSeries.coeff_X_pow_mul',ite_eq_right (by omega)]
  have he:=taylor_finset_sum (Finset.range (K+1))
    (fun i z=>((PowerSeries.coeff i f:ℝ):ℂ)*(g z)^i)
    (by intro i hi;exact analyticAt_const.mul (hg.pow i))
  have hc:=congrArg (PowerSeries.coeff n) he
  change WP.coeff (fun z=>∑i∈Finset.range (K+1),((PowerSeries.coeff i f:ℝ):ℂ)*(g z)^i) n=_
  rw[←taylor_coeff,hc,coeff_subst_finite _ _ hP]
  simp only[map_sum,taylor_const_mul,taylor_pow hg,PowerSeries.coeff_C_mul,PowerSeries.coeff_map,
    Complex.ofRealHom_eq_coe]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkn
  rw[hz k (by have hh:¬k<n+1:=by simpa only[Finset.mem_range] using hkn
              omega),mul_zero]

lemma map_shiftVariable (c:ℝ):PowerSeries.map Complex.ofRealHom (WP.HigherOrder.shiftVariable c)=
    PowerSeries.X*(1-PowerSeries.C (c:ℂ)*PowerSeries.X)⁻¹ := by
  rw[WP.HigherOrder.shiftVariable,map_mul,PowerSeries.map_X,map_inv_ofReal _ (by simp)]
  simp

lemma truncatedSeriesPolynomial_shift_coeff (f:WP.HigherOrder.Series) (c:ℝ)(K n:ℕ)(hn:n≤K):
    WP.coeff (fun z=>truncatedSeriesPolynomial f K (inverseComplexShift c z)) n=
      ((PowerSeries.coeff n (WP.HigherOrder.complexityShift c f):ℝ):ℂ) := by
  rw[truncatedSeriesPolynomial_comp_coeff f _ (inverseComplexShift_analytic c 0 (by simp))
    (inverseComplexShift_zero c) K n hn,inverseComplexShift_taylor]
  have he:=PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero
    (WP.HigherOrder.shiftVariable_constant c)) (h:=Complex.ofRealHom) f
  change PowerSeries.map Complex.ofRealHom (f.subst (WP.HigherOrder.shiftVariable c))=
    (PowerSeries.map Complex.ofRealHom f).subst (PowerSeries.map Complex.ofRealHom (WP.HigherOrder.shiftVariable c)) at he
  rw[map_shiftVariable] at he
  rw[←he]
  rfl


lemma inverseComplexShift_norm (c:ℝ) (z:ℂ) (hz:|c| *‖z‖≤1/2):
    1-(c:ℂ)*z≠0 ∧ ‖inverseComplexShift c z‖≤2*‖z‖ := by
  have hd:1/2≤‖1-(c:ℂ)*z‖:=by
    have he:=norm_sub_norm_le (1:ℂ) ((c:ℂ)*z)
    simp only[norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs] at he
    linarith
  have hp:0<‖1-(c:ℂ)*z‖:=lt_of_lt_of_le (by norm_num) hd
  refine ⟨norm_pos_iff.mp hp,?_⟩
  rw[inverseComplexShift,norm_mul,norm_inv,←div_eq_mul_inv]
  apply (div_le_iff₀ hp).mpr
  nlinarith[norm_nonneg z]

lemma shifted_truncated_polynomial_remainder (f:WP.HigherOrder.Series) (c C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(z:ℂ)(hz:‖z‖≤1/(8*(B+|c|+1)*((K:ℝ)+1))):
    ‖truncatedSeriesPolynomial f K (inverseComplexShift c z)-
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.complexityShift c f):ℝ):ℂ)*z^i‖≤
      4*C*(4*(B+|c|+1)*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)*‖z‖^(K+1) := by
  let B':ℝ:=2*(B+|c|+1)
  have hBp:0<B':=by dsimp[B'];positivity
  have hBB:2*B≤B':=by dsimp[B'];have ha:=abs_nonneg c;linarith
  have hBc:|c|≤B':=by dsimp[B'];have ha:=abs_nonneg c;linarith
  have hKp:0<(K:ℝ)+1:=by positivity
  have hK1:1≤(K:ℝ)+1:=by have hk:=Nat.cast_nonneg (α:=ℝ) K;linarith
  have hdata(w:ℂ)(hw:‖w‖≤1/(2*B'*((K:ℝ)+1))):
      1-(c:ℂ)*w≠0 ∧ ‖truncatedSeriesPolynomial f K (inverseComplexShift c w)‖≤2*C:=by
    have hsmall:|c| *‖w‖≤1/2:=by
      have he:‖w‖*(2*B'*((K:ℝ)+1))≤1:=(le_div_iff₀ (by positivity)).mp hw
      have hd:2*|c|≤2*B'*((K:ℝ)+1):=by nlinarith
      have hm:=mul_le_mul_of_nonneg_right hd (norm_nonneg w)
      nlinarith
    obtain ⟨hne,hns⟩:=inverseComplexShift_norm c w hsmall
    have hs:‖inverseComplexShift c w‖≤1/(2*B*((K:ℝ)+1)):=by
      calc
        _ ≤ 2*‖w‖:=hns
        _ ≤ 2*(1/(2*B'*((K:ℝ)+1))):=mul_le_mul_of_nonneg_left hw (by norm_num)
        _ ≤ 1/(2*B*((K:ℝ)+1)):=by
          rw[mul_one_div]
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          have hm:=mul_le_mul_of_nonneg_right hBB hKp.le
          nlinarith
    exact ⟨hne,truncatedSeriesPolynomial_norm_bound f C B hC hB hf K _ hs⟩
  have hd:DifferentiableOn ℂ (fun w=>truncatedSeriesPolynomial f K (inverseComplexShift c w))
      (Metric.closedBall 0 (1/(2*B'*((K:ℝ)+1)))):=by
    intro w hw
    have hw':‖w‖≤1/(2*B'*((K:ℝ)+1)):=by simpa only[Metric.mem_closedBall,dist_zero_right] using hw
    exact ((truncatedSeriesPolynomial_analytic f K _).comp
      (inverseComplexShift_analytic c w (hdata w hw').1)).differentiableAt.differentiableWithinAt
  have hc:∀w∈Metric.sphere (0:ℂ) (1/(2*B'*((K:ℝ)+1))),
      ‖truncatedSeriesPolynomial f K (inverseComplexShift c w)‖≤2*C:=by
    intro w hw
    exact (hdata w (by simpa only[Metric.mem_closedBall,dist_zero_right] using Metric.sphere_subset_closedBall hw)).2
  have hz':‖z‖≤1/(4*B'*((K:ℝ)+1)):=by convert hz using 1;dsimp[B'];ring
  have he:=complex_taylor_linear_factorial_bound
    (fun w=>truncatedSeriesPolynomial f K (inverseComplexShift c w)) B' (2*C) hBp
    (by positivity) K hd hc z hz'
  have hcoef:(∑i∈Finset.range (K+1),WP.coeff
      (fun w=>truncatedSeriesPolynomial f K (inverseComplexShift c w)) i*z^i)=
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.complexityShift c f):ℝ):ℂ)*z^i:=by
    apply Finset.sum_congr rfl
    intro i hi
    rw[truncatedSeriesPolynomial_shift_coeff f c K i (by have hh:=Finset.mem_range.mp hi;omega)]
  rw[hcoef] at he
  convert he using 1;dsimp[B'];ring


lemma shifted_truncated_polynomial_real_remainder (f:WP.HigherOrder.Series) (c C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(h:ℝ)(hh:0<h)(hu:0<h-c)(hw:8*(B+|c|+1)*((K:ℝ)+1)≤h):
    |inversePowerTruncation f K (h-c)-inversePowerTruncation (WP.HigherOrder.complexityShift c f) K h|≤
      4*C*(4*(B+|c|+1)*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(8*(B+|c|+1)*((K:ℝ)+1)):=by
    rw[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
    exact one_div_le_one_div_of_le (by positivity) hw
  have he:=shifted_truncated_polynomial_remainder f c C B hC hB hf K ((1/h:ℝ):ℂ) hz
  have hs:inverseComplexShift c ((1/h:ℝ):ℂ)=((1/(h-c):ℝ):ℂ):=by
    have hh':(h:ℂ)≠0:=by exact_mod_cast hh.ne'
    have hu':(h:ℂ)-(c:ℂ)≠0:=by exact_mod_cast hu.ne'
    dsimp[inverseComplexShift]
    push_cast
    field_simp
  have hp(s:WP.HigherOrder.Series)(t:ℝ):truncatedSeriesPolynomial s K ((1/t:ℝ):ℂ)=
      ((inversePowerTruncation s K t):ℂ):=by
    rw[truncatedSeriesPolynomial_real]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw[div_pow,one_pow,mul_one_div]
  have hq:(∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.complexityShift c f):ℝ):ℂ)*((1/h:ℝ):ℂ)^i)=
      ((inversePowerTruncation (WP.HigherOrder.complexityShift c f) K h):ℂ):=by
    change truncatedSeriesPolynomial (WP.HigherOrder.complexityShift c f) K ((1/h:ℝ):ℂ)=_
    exact hp _ h
  rw[hs,hp,hq,←Complex.ofReal_sub] at he
  simp only[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh),div_pow,one_pow] at he
  convert he using 1;ring

lemma GevreyOneAsymptotic.shift (F:ℝ→ℝ)(f:WP.HigherOrder.Series)
    (hF:GevreyOneAsymptotic F f)(c:ℝ):
    GevreyOneAsymptotic (fun h=>F (h-c)) (WP.HigherOrder.complexityShift c f):=by
  obtain ⟨C₀,B₀,hC₀,hB₀,hcoeff⟩:=GevreyOneAsymptotic.coeff_bound F f hF
  obtain ⟨C₁,B₁,q,H₀,hC₁,hB₁,hq,hH₀,herr⟩:=hF
  let T:ℝ:=B₀+|c|+1
  have hT:0<T:=by dsimp[T];positivity
  let q':ℝ:=min (q/2) (1/(16*T))
  let H:ℝ:=max (2*H₀+2*|c|+1) (16*T)
  let B:ℝ:=2*B₁+4*T*Real.exp 1
  let C:ℝ:=C₁+4*C₀
  refine ⟨C,B,q',H,by dsimp[C];positivity,by dsimp[B];positivity,
    lt_min (by positivity) (by positivity),
    lt_of_lt_of_le (by positivity) (le_max_right _ _),?_⟩
  intro K h hhH hK
  have hhfirst:2*H₀+2*|c|+1≤h:=(le_max_left _ _).trans hhH
  have hhT:16*T≤h:=(le_max_right _ _).trans hhH
  have hh:0<h:=lt_of_lt_of_le (by positivity) hhT
  have hhalf:0<h/2:=by positivity
  have hu:0<h-c:=by have ha:=le_abs_self c;have hab:=abs_nonneg c;linarith
  have huH:H₀≤h-c:=by have ha:=le_abs_self c;have hab:=abs_nonneg c;linarith
  have hhalfU:h/2≤h-c:=by have ha:=le_abs_self c;have hab:=abs_nonneg c;linarith
  have hKq:(K:ℝ)≤q*(h-c):=by
    have hk:((K:ℝ))≤(q/2)*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hh.le)
    have he:=mul_le_mul_of_nonneg_left hhalfU hq.le
    nlinarith
  have hKr:(K:ℝ)≤(1/(16*T))*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hh.le)
  have hwindow:8*T*((K:ℝ)+1)≤h:=by
    have hk':(K:ℝ)*(16*T)≤h := (le_div_iff₀ (by positivity:0<16*T)).mp
      (by simpa only[one_div,mul_comm,div_eq_mul_inv,one_mul] using hKr)
    nlinarith
  have he:=herr K (h-c) huH hKq
  have hactual:|F (h-c)-inversePowerTruncation f K (h-c)|≤
      C₁*(2*B₁)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
    apply he.trans
    calc
      _ ≤ C₁*B₁^(K+1)*((K+1).factorial:ℝ)/(h/2)^(K+1):=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hhalf _)
          (pow_le_pow_left₀ hhalf.le hhalfU _)
      _ = _:=by rw[div_pow,mul_pow];field_simp
  have htail:=shifted_truncated_polynomial_real_remainder f c C₀ B₀ hC₀.le hB₀ hcoeff K h hh hu hwindow
  have hb₁:2*B₁≤B:=le_add_of_nonneg_right (by positivity)
  have hb₂:4*T*Real.exp 1≤B:=le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ |F (h-c)-inversePowerTruncation f K (h-c)|+
        |inversePowerTruncation f K (h-c)-inversePowerTruncation (WP.HigherOrder.complexityShift c f) K h|:=abs_sub_le _ _ _
    _ ≤ C₁*(2*B₁)^(K+1)*((K+1).factorial:ℝ)/h^(K+1)+
        4*C₀*(4*T*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=add_le_add hactual htail
    _ ≤ C₁*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1)+
        4*C₀*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by gcongr
    _ = _:=by dsimp[C];ring

end WP.Analysis
