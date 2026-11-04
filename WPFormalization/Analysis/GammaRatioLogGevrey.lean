import WPFormalization.Analysis.GammaKernelGlobalRemainder
import WPFormalization.Analysis.WatsonExpansion
/-! A genuine all-order Gevrey-1 error for the actual positive-real shifted
log-Gamma ratio. The exact classical Laplace identity is the only deferred
input. The kernel Taylor bound, its Bernoulli coefficients, exact moments and
uniform factorial remainder are proved locally. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open MeasureTheory Set

private lemma gamma_laplace_nat_integrable (h : ℝ) (hh : 0<h) (n : ℕ) :
    IntegrableOn (fun t:ℝ=>Real.exp (-(h*t))*t^n) (Ioi 0) := by
  simpa only [sub_self,Real.rpow_zero,mul_one] using laplace_monomial_integrable 1 h (by norm_num) hh n

private lemma gamma_laplace_nat_integral (h : ℝ) (hh : 0<h) (n : ℕ) :
    (∫t in Ioi (0:ℝ),Real.exp (-(h*t))*t^n)=(n.factorial:ℝ)/h^(n+1) := by
  have he := laplace_monomial_integral 1 h (by norm_num) hh n
  simp only [sub_self,Real.rpow_zero,mul_one] at he
  have hG : Real.Gamma (1+(n:ℝ))=(n.factorial:ℝ) := by rw [add_comm,Real.Gamma_nat_eq_factorial]
  have hp : 1+(n:ℝ)=((n+1:ℕ):ℝ) := by push_cast;ring
  rw [hG,hp,Real.rpow_natCast] at he
  simpa only [one_div,inv_pow,div_eq_mul_inv,mul_comm,one_mul,mul_one] using he

private lemma gamma_laplace_polynomial (c : ℕ → ℝ) (N : ℕ) (h : ℝ) (hh : 0<h) :
    IntegrableOn (fun t:ℝ=>Real.exp (-(h*t))*(∑i∈Finset.range N,c i*t^i)) (Ioi 0) ∧
    (∫t in Ioi (0:ℝ),Real.exp (-(h*t))*(∑i∈Finset.range N,c i*t^i))=
      ∑i∈Finset.range N,c i*(i.factorial:ℝ)/h^(i+1) := by
  have he : (fun t:ℝ=>Real.exp (-(h*t))*(∑i∈Finset.range N,c i*t^i))=
      (fun t:ℝ=>∑i∈Finset.range N,c i*(Real.exp (-(h*t))*t^i)) := by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hi : ∀i∈Finset.range N,IntegrableOn (fun t:ℝ=>c i*(Real.exp (-(h*t))*t^i)) (Ioi 0) :=
    fun i _=>(gamma_laplace_nat_integrable h hh i).const_mul (c i)
  rw [he]
  refine ⟨integrable_finsetSum _ hi,?_⟩
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul,gamma_laplace_nat_integral h hh i]
    ring
  · exact hi

lemma gammaRatioLog_uniform_factorial_error (a : ℚ) (ha : 0<a) :
    ∃ C B : ℝ,0<C ∧ 0<B ∧ ∀N:ℕ,∀h:ℝ,0<h →
      |Real.log (Real.Gamma (h+(a:ℝ)))-Real.log (Real.Gamma h)-(a:ℝ)*Real.log h-
        ∑j∈Finset.range (N+1),PowerSeries.coeff j (WP.HigherOrder.gammaRatioLog a)/h^j|≤
      C*B^N*(N.factorial:ℝ)/h^(N+1) := by
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  obtain ⟨C,B,hC,hB,hbound⟩ := gammaLogRatioKernel_global_taylor_bound (a:ℝ) haR
  refine ⟨C,B,hC,hB,?_⟩
  intro N h hh
  let c : ℕ → ℝ := WP.realCoeff (gammaRatioKernel (a:ℝ))
  let P : ℝ → ℝ := fun t=>∑i∈Finset.range N,c i*t^i
  let R : ℝ → ℝ := fun t=>External.gammaLogRatioKernel (a:ℝ) t-P t
  have hRm : AEStronglyMeasurable R (volume.restrict (Ioi 0)) := by
    have hm : Measurable R := by dsimp [R,P,External.gammaLogRatioKernel];fun_prop
    exact hm.aestronglyMeasurable
  have hRb : ∀t∈Ioi (0:ℝ),‖R t‖≤(C*B^N)*t^N := by
    intro t ht
    simpa only [R,P,c,Real.norm_eq_abs] using hbound N t ht
  have hw := laplace_power_remainder_bound R (Ioi 0) measurableSet_Ioi (by rfl) 1 h (C*B^N) N
    (by norm_num) hh (by positivity) hRm hRb
  simp only [sub_self,Real.rpow_zero,mul_one,smul_eq_mul] at hw
  have hG : Real.Gamma (1+(N:ℝ))=(N.factorial:ℝ) := by rw [add_comm,Real.Gamma_nat_eq_factorial]
  have hp : (1/h)^(1+(N:ℝ))=1/h^(N+1) := by
    rw [show 1+(N:ℝ)=((N+1:ℕ):ℝ) by push_cast;ring,Real.rpow_natCast,div_pow,one_pow]
  have hrem : |∫t in Ioi (0:ℝ),Real.exp (-(h*t))*R t|≤C*B^N*(N.factorial:ℝ)/h^(N+1) := by
    calc
      _ ≤ (C*B^N)*((1/h)^(1+(N:ℝ))*Real.Gamma (1+(N:ℝ))) := by
        simpa only [Real.norm_eq_abs] using hw.2
      _ = _ := by rw [hp,hG];ring
  obtain ⟨hg,hgEq⟩ := External.log_gamma_ratio_laplace h (a:ℝ) hh haR
  simp only [neg_mul] at hg hgEq
  have hPi := gamma_laplace_polynomial c N h hh
  have hpoly : (∫t in Ioi (0:ℝ),Real.exp (-(h*t))*P t)=
      ∑j∈Finset.range (N+1),PowerSeries.coeff j (WP.HigherOrder.gammaRatioLog a)/h^j := by
    rw [hPi.2]
    have hc (i : ℕ) : c i*(i.factorial:ℝ)=PowerSeries.coeff (i+1) (WP.HigherOrder.gammaRatioLog a) :=
      gammaRatioKernel_realCoeff_log a i
    simp_rw [hc]
    rw [Finset.sum_range_succ']
    simp only [PowerSeries.coeff_zero_eq_constantCoeff,WP.HigherOrder.gammaRatioLog_constant,zero_div,add_zero]
  have hdiff : (∫t in Ioi (0:ℝ),Real.exp (-(h*t))*R t)=
      (∫t in Ioi (0:ℝ),Real.exp (-(h*t))*External.gammaLogRatioKernel (a:ℝ) t)-
        (∫t in Ioi (0:ℝ),Real.exp (-(h*t))*P t) := by
    dsimp only [R]
    simp_rw [mul_sub]
    exact integral_sub hg hPi.1
  rw [hdiff,←hgEq,hpoly] at hrem
  exact hrem


lemma gammaRatioLog_uniform_gevrey_error (a : ℚ) (ha : 0<a) :
    ∃ C B : ℝ,0<C ∧ 0<B ∧ ∀K:ℕ,∀h:ℝ,0<h →
      |Real.log (Real.Gamma (h+(a:ℝ)))-Real.log (Real.Gamma h)-(a:ℝ)*Real.log h-
        ∑j∈Finset.range (K+1),PowerSeries.coeff j (WP.HigherOrder.gammaRatioLog a)/h^j|≤
      C*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1) := by
  obtain ⟨C,B,hC,hB,herr⟩ := gammaRatioLog_uniform_factorial_error a ha
  let B' : ℝ := max B 1
  have hB1 : 1≤B' := le_max_right _ _
  have hB0 : 0≤B' := by linarith
  refine ⟨C,B',hC,lt_of_lt_of_le zero_lt_one hB1,?_⟩
  intro K h hh
  apply (herr K h hh).trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hh.le _)
  have hpow : B^K≤B'^(K+1) :=
    (pow_le_pow_left₀ hB.le (le_max_left B 1) K).trans (pow_le_pow_right₀ hB1 (Nat.le_succ K))
  have hfact : (K.factorial:ℝ)≤((K+1).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ K)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hC.le) hfact (Nat.cast_nonneg _)
    (mul_nonneg hC.le (pow_nonneg hB0 _))

end WP.Analysis
