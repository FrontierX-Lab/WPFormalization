import WPFormalization.HigherOrder.PoissonCentralPolynomials
import WPFormalization.Analysis.GammaRatioBernoulli
/-! The actual normalized Poisson coefficient operator from Appendix D.6.
Its central moments are the prescribed D.19 polynomials; finite Taylor
polynomials and the uniform operator norm are proved for the genuine
complex derivative coefficient. The growing-order analytic remainder in
Lemma D.6 remains a separate obligation. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
open scoped Topology

/- The actual normalized coefficient operator in Appendix D.6. -/
def poissonCoefficientOperator (h : ℝ) (k : ℕ) (f : ℂ → ℂ) : ℂ :=
  (k.factorial : ℂ)/(h : ℂ)^k * WP.coeff (fun u => Complex.exp ((h:ℂ)*u)*f u) k

lemma poissonCoefficientOperator_zero (h : ℝ) (f : ℂ → ℂ) :
    poissonCoefficientOperator h 0 f=f 0 := by
  simp [poissonCoefficientOperator,WP.coeff]

lemma poissonCoefficientOperator_const_mul (h : ℝ) (k : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    poissonCoefficientOperator h k (fun u=>c*f u)=c*poissonCoefficientOperator h k f := by
  have he : (fun u : ℂ=>Complex.exp ((h:ℂ)*u)*(c*f u))=
      (fun u : ℂ=>c*(Complex.exp ((h:ℂ)*u)*f u)) := by funext u;ring
  unfold poissonCoefficientOperator
  rw [he,←Analysis.taylor_coeff,Analysis.taylor_const_mul,PowerSeries.coeff_C_mul,Analysis.taylor_coeff]
  ring

lemma poissonCoefficientOperator_sum {ι : Type*} (h : ℝ) (k : ℕ) (s : Finset ι)
    (f : ι → ℂ → ℂ) (hf : ∀i∈s,AnalyticAt ℂ (f i) 0) :
    poissonCoefficientOperator h k (fun u=>∑i∈s,f i u)=
      ∑i∈s,poissonCoefficientOperator h k (f i) := by
  have he : (fun u : ℂ=>Complex.exp ((h:ℂ)*u)*(∑i∈s,f i u))=
      (fun u : ℂ=>∑i∈s,Complex.exp ((h:ℂ)*u)*f i u) := by funext u;exact Finset.mul_sum _ _ _
  have hexp : AnalyticAt ℂ (fun u : ℂ => Complex.exp ((h:ℂ)*u)) 0 := by fun_prop
  unfold poissonCoefficientOperator
  rw [he,←Analysis.taylor_coeff,Analysis.taylor_finset_sum s _ (by intro i hi;exact hexp.mul (hf i hi)),map_sum,Finset.mul_sum]
  simp only [Analysis.taylor_coeff]

lemma exp_mul_monomial_coeff (h : ℂ) (k i : ℕ) :
    WP.coeff (fun u=>Complex.exp (h*u)*u^i) k=
      if i ≤ k then h^(k-i)/( (k-i).factorial:ℂ) else 0 := by
  rw [←Analysis.taylor_coeff,Analysis.taylor_mul (by fun_prop) (by fun_prop),
    Analysis.taylor_exp_const_mul,Analysis.taylor_pow (f:=fun u : ℂ=>u) analyticAt_id,Analysis.taylor_id,
    mul_comm,PowerSeries.coeff_X_pow_mul']
  split_ifs with hi
  · simp [PowerSeries.coeff_rescale,PowerSeries.coeff_exp,div_eq_mul_inv]
  · rfl

lemma poissonCoefficientOperator_monomial (h : ℝ) (hh : h≠0) (k i : ℕ) :
    poissonCoefficientOperator h k (fun u=>u^i)=(k.descFactorial i:ℂ)/(h:ℂ)^i := by
  have hc : (h:ℂ)≠0 := by exact_mod_cast hh
  rw [poissonCoefficientOperator,exp_mul_monomial_coeff]
  by_cases hi : i ≤ k
  · rw [ite_eq_left hi]
    have hfac : ((k-i).factorial:ℂ)*(k.descFactorial i:ℂ)=(k.factorial:ℂ) := by exact_mod_cast Nat.factorial_mul_descFactorial hi
    have hpow : (h:ℂ)^k=(h:ℂ)^(k-i)*(h:ℂ)^i := by rw [←pow_add,Nat.sub_add_cancel hi]
    rw [←hfac,hpow]
    field_simp [hc,show ((k-i).factorial:ℂ)≠0 by exact_mod_cast (k-i).factorial_ne_zero]
  · rw [ite_eq_right hi,Nat.descFactorial_of_lt (by omega)]
    simp

lemma one_add_power_coeff (k i : ℕ) :
    WP.coeff (fun z : ℂ=>(1+z)^k) i=(k.choose i:ℂ) := by
  rw [←Analysis.taylor_coeff,Analysis.taylor_pow (by fun_prop),
    Analysis.taylor_add (f:=fun _ : ℂ=>1) (g:=fun z : ℂ=>z) analyticAt_const analyticAt_id,Analysis.taylor_const,Analysis.taylor_id,map_one]
  have he : ((1+PowerSeries.X:PowerSeries ℂ)^k)=(((1+Polynomial.X:Polynomial ℂ)^k):PowerSeries ℂ) := by simp
  rw [he,←Polynomial.coe_pow,Polynomial.coeff_coe,Polynomial.coeff_one_add_X_pow]

lemma poissonCentralPolynomial_binomial (m k : ℕ) :
    (((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ)=
      ∑i∈Finset.range (m+1),(m.choose i:ℂ)*(-(k:ℂ))^(m-i)*(k.descFactorial i:ℂ) := by
  rw [poissonCentralPolynomial_generating_nat]
  have he : (fun z : ℂ=>Complex.exp (-(k:ℂ)*z)*(1+z)^k)=
      (fun z : ℂ=>(1+z)^k*Complex.exp (-(k:ℂ)*z)) := by funext z;ring
  rw [he,←Analysis.taylor_coeff,Analysis.taylor_mul (by fun_prop) (by fun_prop),
    PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := by have ht:=Finset.mem_range.mp hi;omega
  rw [Analysis.taylor_coeff,one_add_power_coeff,Analysis.taylor_exp_const_mul,
    PowerSeries.coeff_rescale,PowerSeries.coeff_exp,Nat.descFactorial_eq_factorial_mul_choose]
  simp only [map_inv₀,map_natCast,one_div,Nat.cast_mul]
  rw [Nat.cast_choose ℂ him]
  field_simp [show (i.factorial:ℂ)≠0 by exact_mod_cast i.factorial_ne_zero,show ((m-i).factorial:ℂ)≠0 by exact_mod_cast (m-i).factorial_ne_zero]

lemma poissonCoefficientOperator_central_moment (h : ℝ) (hh : h≠0) (k m : ℕ) :
    poissonCoefficientOperator h k (fun u=>(u-(k:ℂ)/(h:ℂ))^m)=
      (((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ)/(h:ℂ)^m := by
  have hc : (h:ℂ)≠0 := by exact_mod_cast hh
  have he : (fun u : ℂ=>(u-(k:ℂ)/(h:ℂ))^m)=
      (fun u=>∑i∈Finset.range (m+1),
        ((-(k:ℂ)/(h:ℂ))^(m-i)*(m.choose i:ℂ))*u^i) := by
    funext u
    rw [sub_eq_add_neg,neg_div,add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he,poissonCoefficientOperator_sum h k _ _ (by intro i hi;fun_prop),
    poissonCentralPolynomial_binomial,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [poissonCoefficientOperator_const_mul,poissonCoefficientOperator_monomial h hh]
  have him : i ≤ m := by have ht:=Finset.mem_range.mp hi;omega
  have hpow : (h:ℂ)^m=(h:ℂ)^(m-i)*(h:ℂ)^i := by rw [←pow_add,Nat.sub_add_cancel him]
  rw [div_pow,hpow]
  field_simp

lemma poissonCoefficientOperator_centered_polynomial (h : ℝ) (hh : h≠0) (k : ℕ)
    (s : Finset ℕ) (a : ℕ → ℂ) :
    poissonCoefficientOperator h k (fun u=>∑m∈s,a m*(u-(k:ℂ)/(h:ℂ))^m)=
      ∑m∈s,a m*((((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ)/(h:ℂ)^m) := by
  rw [poissonCoefficientOperator_sum h k s _ (by intro m hm;fun_prop)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [poissonCoefficientOperator_const_mul,poissonCoefficientOperator_central_moment h hh]

lemma poissonCoefficientOperator_finite_formula (h : ℝ) (hh : h≠0) (k : ℕ)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    poissonCoefficientOperator h k f=
      ∑i∈Finset.range (k+1),WP.coeff f i*(k.descFactorial i:ℂ)/(h:ℂ)^i := by
  have he : (fun u : ℂ=>Complex.exp ((h:ℂ)*u)*f u)=
      (fun u : ℂ=>f u*Complex.exp ((h:ℂ)*u)) := by funext u;ring
  unfold poissonCoefficientOperator
  rw [he,←Analysis.taylor_coeff,Analysis.taylor_mul hf (by fun_prop),
    PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by have ht:=Finset.mem_range.mp hi;omega
  simp only [Analysis.taylor_coeff]
  have ht := poissonCoefficientOperator_monomial h hh k i
  rw [poissonCoefficientOperator,exp_mul_monomial_coeff,ite_eq_left hik] at ht
  have hec : WP.coeff (fun u : ℂ=>Complex.exp ((h:ℂ)*u)) (k-i)=
      (h:ℂ)^(k-i)/((k-i).factorial:ℂ) := by
    rw [←Analysis.taylor_coeff,Analysis.taylor_exp_const_mul]
    simp [PowerSeries.coeff_rescale,PowerSeries.coeff_exp,div_eq_mul_inv]
  rw [hec]
  calc _ = WP.coeff f i*((k.factorial:ℂ)/(h:ℂ)^k*((h:ℂ)^(k-i)/((k-i).factorial:ℂ))) := by ring
       _ = _ := by rw [ht];ring

lemma poissonCoefficientOperator_norm_le_of_coeff_bound (h R M : ℝ) (hh : 0 < h)
    (hR : 0 < R) (hM : 0 ≤ M) (k : ℕ) (hk : (k:ℝ)/h ≤ R/2)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hb : ∀i,‖WP.coeff f i‖ ≤ M/R^i) :
    ‖poissonCoefficientOperator h k f‖ ≤ 2*M := by
  rw [poissonCoefficientOperator_finite_formula h hh.ne' k f hf]
  calc _ ≤ ∑i∈Finset.range (k+1),‖WP.coeff f i*(k.descFactorial i:ℂ)/(h:ℂ)^i‖ := norm_sum_le _ _
       _ ≤ ∑i∈Finset.range (k+1),M*(1/2:ℝ)^i := by
        apply Finset.sum_le_sum
        intro i hi
        have hd : (k.descFactorial i:ℝ) ≤ (k:ℝ)^i := by exact_mod_cast Nat.descFactorial_le_pow k i
        have hscale : (k:ℝ)/(h*R) ≤ 1/2 := by
          apply (div_le_iff₀ (mul_pos hh hR)).mpr
          have ht := (div_le_iff₀ hh).mp hk
          nlinarith
        rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
        have hn : ‖(k.descFactorial i:ℂ)‖=(k.descFactorial i:ℝ) := by simp
        rw [hn]
        calc _ ≤ (M/R^i)*(k:ℝ)^i/h^i := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul (hb i) hd (by positivity) (by positivity)
             _ = M*((k:ℝ)/(h*R))^i := by rw [div_pow,mul_pow];field_simp
             _ ≤ M*(1/2:ℝ)^i := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hscale i) hM
       _ = M*∑i∈Finset.range (k+1),(1/2:ℝ)^i := (Finset.mul_sum _ _ _).symm
       _ ≤ M*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) hM
       _ = _ := by ring

lemma poissonCoefficientOperator_norm_le (h R M : ℝ) (hh : 0 < h)
    (hR : 0 < R) (hM : 0 ≤ M) (k : ℕ) (hk : (k:ℝ)/h ≤ R/2)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hb : ∀z∈Metric.sphere (0:ℂ) R,‖f z‖ ≤ M) :
    ‖poissonCoefficientOperator h k f‖ ≤ 2*M := by
  apply poissonCoefficientOperator_norm_le_of_coeff_bound h R M hh hR hM k hk f
    (hf 0 (by simp [hR.le]))
  exact Analysis.coeff_norm_le_circle_bound f R M hR hf.differentiableOn hb

end WP.HigherOrder
