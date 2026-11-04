import WPFormalization.Analysis.GevreyOneMatching
/-! Actual unit-series inversion with a uniform linear-window factorial error. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open PowerSeries Filter
open scoped Topology

lemma coeff_inv_eq_of_coeff_eq (F G:PowerSeries ℂ) (N:ℕ)
    (hFG:∀i≤N,PowerSeries.coeff i F=PowerSeries.coeff i G)
    (n:ℕ)(hn:n≤N):PowerSeries.coeff n (F⁻¹)=PowerSeries.coeff n (G⁻¹):=by
  have h0:PowerSeries.constantCoeff F=PowerSeries.constantCoeff G:=by
    simpa only[PowerSeries.coeff_zero_eq_constantCoeff] using hFG 0 (Nat.zero_le N)
  induction n using Nat.strong_induction_on with
  | h n ih=>
    rw[PowerSeries.coeff_inv,PowerSeries.coeff_inv,h0]
    by_cases hn0:n=0
    · simp only[ite_eq_left hn0]
    · simp only[ite_eq_right hn0]
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      have he:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      by_cases hlt:ij.2<n
      · simp only[ite_eq_left hlt]
        rw[hFG ij.1 (by omega),ih ij.2 hlt (by omega)]
      · simp only[ite_eq_right hlt]

lemma truncatedSeriesPolynomial_inv_coeff (f:WP.HigherOrder.Series)
    (hf0:PowerSeries.constantCoeff f=1)(K n:ℕ)(hn:n≤K):
    WP.coeff (fun z=>(truncatedSeriesPolynomial f K z)⁻¹) n=
      ((PowerSeries.coeff n (f⁻¹):ℝ):ℂ):=by
  have h0:truncatedSeriesPolynomial f K 0=1:=by
    have he:=truncatedSeriesPolynomial_coeff f K 0
    simpa only[WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,
      ite_eq_left (Nat.zero_le K),PowerSeries.coeff_zero_eq_constantCoeff,hf0,Complex.ofReal_one] using he
  rw[←taylor_coeff,taylor_inv (truncatedSeriesPolynomial_analytic f K 0) (by rw[h0];exact one_ne_zero)]
  have hc:∀i≤K,PowerSeries.coeff i (taylor (truncatedSeriesPolynomial f K))=
      PowerSeries.coeff i (PowerSeries.map Complex.ofRealHom f):=by
    intro i hi
    rw[taylor_coeff,truncatedSeriesPolynomial_coeff,ite_eq_left hi,PowerSeries.coeff_map]
    rfl
  rw[coeff_inv_eq_of_coeff_eq _ _ K hc n hn,←map_inv_ofReal f (by rw[hf0];exact one_ne_zero)]
  rfl

lemma truncatedSeriesPolynomial_sub_const_norm (f:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(z:ℂ)(hz:‖z‖≤1/(2*B*((K:ℝ)+1))):
    ‖truncatedSeriesPolynomial f K z-((PowerSeries.coeff 0 f:ℝ):ℂ)‖≤
      2*C*B*((K:ℝ)+1)*‖z‖:=by
  let q:ℝ:=B*((K:ℝ)+1)*‖z‖
  have hq0:0≤q:=by dsimp[q];positivity
  have hq:q≤1/2:=by
    have he:‖z‖*(2*B*((K:ℝ)+1))≤1:=(le_div_iff₀ (by positivity)).mp hz
    dsimp[q]
    nlinarith
  have he:truncatedSeriesPolynomial f K z-((PowerSeries.coeff 0 f:ℝ):ℂ)=
      ∑i∈Finset.range K,((PowerSeries.coeff (i+1) f:ℝ):ℂ)*z^(i+1):=by
    rw[truncatedSeriesPolynomial,Finset.sum_range_succ']
    simp only[pow_zero,mul_one]
    ring
  have ht(i:ℕ)(hi:i∈Finset.range K):
      ‖((PowerSeries.coeff (i+1) f:ℝ):ℂ)*z^(i+1)‖≤C*q*(1/(2:ℝ))^i:=by
    have hiK:i+1≤K:=by have hh:=Finset.mem_range.mp hi;omega
    rw[norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (C*B^(i+1)*((i+1).factorial:ℝ))*‖z‖^(i+1):=
        mul_le_mul_of_nonneg_right (hf (i+1)) (by positivity)
      _ ≤ (C*B^(i+1)*((K:ℝ)+1)^(i+1))*‖z‖^(i+1):=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (factorial_le_order_pow (i+1) K hiK) (by positivity)) (by positivity)
      _ = C*q^(i+1):=by dsimp[q];simp only[mul_pow];ring
      _ ≤ C*q*(1/(2:ℝ))^i:=by
        rw[pow_succ]
        have hp:=pow_le_pow_left₀ hq0 hq i
        calc
          _ = (C*q)*q^i:=by ring
          _ ≤ _:=mul_le_mul_of_nonneg_left hp (mul_nonneg hC hq0)
  rw[he]
  calc
    _ ≤ ∑i∈Finset.range K,‖((PowerSeries.coeff (i+1) f:ℝ):ℂ)*z^(i+1)‖:=norm_sum_le _ _
    _ ≤ ∑i∈Finset.range K,C*q*(1/(2:ℝ))^i:=Finset.sum_le_sum ht
    _ = C*q*∑i∈Finset.range K,(1/(2:ℝ))^i:=(Finset.mul_sum _ _ _).symm
    _ ≤ C*q*2:=mul_le_mul_of_nonneg_left (sum_geometric_two_le K) (by positivity)
    _ = _:=by dsimp[q];ring


lemma truncatedSeriesPolynomial_unit_data (f:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf0:PowerSeries.constantCoeff f=1)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(z:ℂ)(hz:‖z‖≤1/(8*(C+1)*B*((K:ℝ)+1))):
    ‖truncatedSeriesPolynomial f K z-1‖≤1/2 ∧
      truncatedSeriesPolynomial f K z≠0 ∧ ‖(truncatedSeriesPolynomial f K z)⁻¹‖≤2:=by
  let B':ℝ:=4*(C+1)*B
  have hBp:0<B':=by dsimp[B'];positivity
  have hBB:B≤B':=by dsimp[B'];nlinarith[mul_nonneg hC hB.le]
  have hBC:2*C*B≤B':=by dsimp[B'];nlinarith[mul_nonneg hC hB.le]
  have hN:0<(K:ℝ)+1:=by positivity
  have hz':‖z‖≤1/(2*B'*((K:ℝ)+1)):=by convert hz using 1;dsimp[B'];ring
  have hzB:‖z‖≤1/(2*B*((K:ℝ)+1)):=by
    apply hz'.trans
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have hp:=truncatedSeriesPolynomial_sub_const_norm f C B hC hB hf K z hzB
  have hc:((PowerSeries.coeff 0 f:ℝ):ℂ)=1:=by simp only[PowerSeries.coeff_zero_eq_constantCoeff,hf0,Complex.ofReal_one]
  rw[hc] at hp
  have hsmall:‖truncatedSeriesPolynomial f K z-1‖≤1/2:=by
    apply hp.trans
    have he:‖z‖*(2*B'*((K:ℝ)+1))≤1:=(le_div_iff₀ (by positivity)).mp hz'
    have hm:=mul_le_mul_of_nonneg_right hBC (mul_nonneg hN.le (norm_nonneg z))
    nlinarith
  have hnorm:1/2≤‖truncatedSeriesPolynomial f K z‖:=by
    have he:=norm_sub_norm_le (1:ℂ) (truncatedSeriesPolynomial f K z)
    rw[norm_one,norm_sub_rev] at he
    linarith
  have hp0:0<‖truncatedSeriesPolynomial f K z‖:=lt_of_lt_of_le (by norm_num) hnorm
  refine ⟨hsmall,norm_pos_iff.mp hp0,?_⟩
  rw[norm_inv,←one_div]
  apply (div_le_iff₀ hp0).mpr
  linarith

lemma inverse_truncated_polynomial_remainder (f:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf0:PowerSeries.constantCoeff f=1)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(z:ℂ)(hz:‖z‖≤1/(16*(C+1)*B*((K:ℝ)+1))):
    ‖(truncatedSeriesPolynomial f K z)⁻¹-
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (f⁻¹):ℝ):ℂ)*z^i‖≤
      4*(8*(C+1)*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)*‖z‖^(K+1):=by
  let B':ℝ:=4*(C+1)*B
  have hBp:0<B':=by dsimp[B'];positivity
  have hdata(w:ℂ)(hw:‖w‖≤1/(2*B'*((K:ℝ)+1))):
      truncatedSeriesPolynomial f K w≠0 ∧ ‖(truncatedSeriesPolynomial f K w)⁻¹‖≤2:=by
    exact (truncatedSeriesPolynomial_unit_data f C B hC hB hf0 hf K w
      (by convert hw using 1;dsimp[B'];ring)).2
  have hd:DifferentiableOn ℂ (fun w=>(truncatedSeriesPolynomial f K w)⁻¹)
      (Metric.closedBall 0 (1/(2*B'*((K:ℝ)+1)))):=by
    intro w hw
    have hw':‖w‖≤1/(2*B'*((K:ℝ)+1)):=by simpa only[Metric.mem_closedBall,dist_zero_right] using hw
    exact ((truncatedSeriesPolynomial_analytic f K w).inv (hdata w hw').1).differentiableAt.differentiableWithinAt
  have hc:∀w∈Metric.sphere (0:ℂ) (1/(2*B'*((K:ℝ)+1))),‖(truncatedSeriesPolynomial f K w)⁻¹‖≤2:=by
    intro w hw
    exact (hdata w (by simpa only[Metric.mem_closedBall,dist_zero_right] using Metric.sphere_subset_closedBall hw)).2
  have hz':‖z‖≤1/(4*B'*((K:ℝ)+1)):=by convert hz using 1;dsimp[B'];ring
  have he:=complex_taylor_linear_factorial_bound (fun w=>(truncatedSeriesPolynomial f K w)⁻¹)
    B' 2 hBp (by norm_num) K hd hc z hz'
  have hcoef:(∑i∈Finset.range (K+1),WP.coeff (fun w=>(truncatedSeriesPolynomial f K w)⁻¹) i*z^i)=
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (f⁻¹):ℝ):ℂ)*z^i:=by
    apply Finset.sum_congr rfl
    intro i hi
    rw[truncatedSeriesPolynomial_inv_coeff f hf0 K i (by have hh:=Finset.mem_range.mp hi;omega)]
  rw[hcoef] at he
  convert he using 1;dsimp[B'];ring


lemma inverse_truncated_polynomial_real_remainder (f:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf0:PowerSeries.constantCoeff f=1)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(h:ℝ)(hh:0<h)(hw:16*(C+1)*B*((K:ℝ)+1)≤h):
    |(inversePowerTruncation f K h)⁻¹-inversePowerTruncation (f⁻¹) K h|≤
      4*(8*(C+1)*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(16*(C+1)*B*((K:ℝ)+1)):=by
    rw[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
    exact one_div_le_one_div_of_le (by positivity) hw
  have he:=inverse_truncated_polynomial_remainder f C B hC hB hf0 hf K ((1/h:ℝ):ℂ) hz
  have hp(s:WP.HigherOrder.Series):truncatedSeriesPolynomial s K ((1/h:ℝ):ℂ)=
      ((inversePowerTruncation s K h):ℂ):=by
    rw[truncatedSeriesPolynomial_real]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw[div_pow,one_pow,mul_one_div]
  have hq:(∑i∈Finset.range (K+1),((PowerSeries.coeff i (f⁻¹):ℝ):ℂ)*((1/h:ℝ):ℂ)^i)=
      ((inversePowerTruncation (f⁻¹) K h):ℂ):=by
    change truncatedSeriesPolynomial (f⁻¹) K ((1/h:ℝ):ℂ)=_
    exact hp (f⁻¹)
  rw[hp,hq,←Complex.ofReal_inv,←Complex.ofReal_sub] at he
  simp only[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh),div_pow,one_pow] at he
  convert he using 1;ring

lemma inv_abs_le_two_of_unit_close (x:ℝ)(hx:|x-1|≤1/2):x≠0 ∧ |x⁻¹|≤2:=by
  have he:1-|x|≤|x-1|:=by
    simpa only[norm_one,Real.norm_eq_abs,abs_sub_comm] using norm_sub_norm_le (1:ℝ) x
  have hn:1/2≤|x|:=by linarith
  have hp:0< |x|:=lt_of_lt_of_le (by norm_num) hn
  refine ⟨abs_pos.mp hp,?_⟩
  rw[abs_inv,←one_div]
  apply (div_le_iff₀ hp).mpr
  linarith

lemma inverse_value_truncation_error (f:WP.HigherOrder.Series)(C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf0:PowerSeries.constantCoeff f=1)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ)(h:ℝ)(hh:0<h)(hw:16*(C+1)*B*((K:ℝ)+1)≤h)
    (x E:ℝ)(hx0:|x-1|≤1/2)(hx:|x-inversePowerTruncation f K h|≤E):
    |x⁻¹-inversePowerTruncation (f⁻¹) K h|≤4*E+
      4*(8*(C+1)*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
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
  obtain ⟨hxne,hxi⟩:=inv_abs_le_two_of_unit_close x hx0
  obtain ⟨hpne,hpi⟩:=inv_abs_le_two_of_unit_close _ hP0
  have hE:0≤E:=(abs_nonneg _).trans hx
  have hdiff:|x⁻¹-(inversePowerTruncation f K h)⁻¹|≤4*E:=by
    have he:x⁻¹-(inversePowerTruncation f K h)⁻¹=
        (inversePowerTruncation f K h-x)*x⁻¹*(inversePowerTruncation f K h)⁻¹:=by
      field_simp
    rw[he,abs_mul,abs_mul,abs_sub_comm]
    have h₁:=mul_le_mul hx hxi (abs_nonneg _) hE
    have h₂:=mul_le_mul h₁ hpi (abs_nonneg _) (by positivity)
    nlinarith
  have htail:=inverse_truncated_polynomial_real_remainder f C B hC hB hf0 hf K h hh hw
  exact (abs_sub_le _ _ _).trans (add_le_add hdiff htail)


lemma GevreyOneAsymptotic.inv_unit (F:ℝ→ℝ)(f:WP.HigherOrder.Series)
    (hF:GevreyOneAsymptotic F f)(hf0:PowerSeries.constantCoeff f=1):
    GevreyOneAsymptotic (fun h=>(F h)⁻¹) (f⁻¹):=by
  obtain ⟨C₀,B₀,hC₀,hB₀,hcoeff⟩:=GevreyOneAsymptotic.coeff_bound F f hF
  obtain ⟨C₁,B₁,q,H₀,hC₁,hB₁,hq,hH₀,herr⟩:=hF
  let T:ℝ:=(C₀+1)*B₀
  have hT:0<T:=by dsimp[T];positivity
  let q':ℝ:=min q (1/(32*T))
  let H:ℝ:=max H₀ (max (32*T) (2*C₁*B₁+1))
  let B:ℝ:=B₁+8*T*Real.exp 1
  let C:ℝ:=4*C₁+4
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
  have he:=inverse_value_truncation_error f C₀ B₀ hC₀.le hB₀ hf0 hcoeff K h hh (by simpa only[T,mul_assoc] using hwindow)
    (F h) (C₁*B₁^(K+1)*((K+1).factorial:ℝ)/h^(K+1)) hx0 (herr K h hh₀ hKq)
  have hb₁:B₁≤B:=le_add_of_nonneg_right (by positivity)
  have hb₂:8*T*Real.exp 1≤B:=le_add_of_nonneg_left hB₁.le
  calc
    _ ≤ 4*(C₁*B₁^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        4*(8*T*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by simpa only[T,mul_assoc] using he
    _ ≤ 4*(C₁*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        4*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by gcongr
    _ = _:=by dsimp[C];ring

end WP.Analysis
