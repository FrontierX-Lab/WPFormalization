import WPFormalization.Analysis.GaussianTaylorRemainder
import WPFormalization.Analysis.FiniteExpTaylor
import WPFormalization.Analysis.CoefficientScaling
set_option maxHeartbeats 800000
/-! Exact finite polynomial coefficients in the pre-Morse stationary expansion. Taylor coefficients of exp(w² beta(tau*w))*a(tau*w) are regraded by genuine finite power-series identities, and their full even Gaussian moments are evaluated. This does not assume equality with the prescribed extraction recipe. -/
noncomputable section
open MeasureTheory
namespace WP.Analysis
lemma exp_subst_mul_coeff_finite (P Q:PowerSeries ℂ)
    (hP:PowerSeries.constantCoeff P=0) (n:ℕ) :
    PowerSeries.coeff n ((PowerSeries.exp ℂ).subst P*Q)=
      ∑j ∈ Finset.range (n+1),PowerSeries.coeff n (P^j*Q)/(j.factorial:ℂ) := by
  have hzero (i j:ℕ)(hij:i<j):PowerSeries.coeff i (P^j)=0 := by
    obtain ⟨T,hT⟩:=PowerSeries.X_dvd_iff.mpr hP
    rw [hT,mul_pow,PowerSeries.coeff_X_pow_mul',ite_eq_right (by omega)]
  have hcoeff (i:ℕ)(hi:i ≤ n):PowerSeries.coeff i ((PowerSeries.exp ℂ).subst P)=
      ∑j ∈ Finset.range (n+1),PowerSeries.coeff i (P^j)/(j.factorial:ℂ) := by
    rw [exp_subst_coeff_finite P hP i]
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hji
    have hij:i<j := by simp only [Finset.mem_range] at hji;omega
    rw [hzero i j hij,zero_div]
  rw [PowerSeries.coeff_mul]
  calc _ = ∑v ∈ Finset.HasAntidiagonal.antidiagonal n,∑j ∈ Finset.range (n+1),
          (PowerSeries.coeff v.1 (P^j)*PowerSeries.coeff v.2 Q)/(j.factorial:ℂ) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [hcoeff v.1 (by have he:=Finset.HasAntidiagonal.mem_antidiagonal.mp hv;omega),Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j hj
            ring
       _ = ∑j ∈ Finset.range (n+1),∑v ∈ Finset.HasAntidiagonal.antidiagonal n,
          (PowerSeries.coeff v.1 (P^j)*PowerSeries.coeff v.2 Q)/(j.factorial:ℂ) := Finset.sum_comm
       _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [PowerSeries.coeff_mul,Finset.sum_div]

lemma coeff_complex_scale_right (f:ℂ → ℂ) (w:ℂ) (n:ℕ) :
    WP.coeff (fun τ:ℂ=>f (τ*w)) n=w^n*WP.coeff f n := by
  have he:(fun τ:ℂ=>f (τ*w))=(fun τ:ℂ=>f (w*τ)) := by funext τ;rw [mul_comm]
  rw [he,WP.coeff,iteratedDeriv_comp_mul_left,mul_zero,mul_div_assoc]
  rfl

lemma stationary_taylor_coefficient_formula (β a:ℂ → ℂ) (hβ:AnalyticAt ℂ β 0)
    (ha:AnalyticAt ℂ a 0) (hβ0:β 0=0) (w:ℂ) (n:ℕ) :
    WP.coeff (fun τ:ℂ=>Complex.exp (w^2*β (τ*w))*a (τ*w)) n=
      ∑j ∈ Finset.range (n+1),w^(n+2*j)*WP.coeff (fun z:ℂ=>β z^j*a z) n/(j.factorial:ℂ) := by
  let F:ℂ → ℂ:=fun τ=>w^2*β (τ*w)
  let A:ℂ → ℂ:=fun τ=>a (τ*w)
  have hm:AnalyticAt ℂ (fun τ:ℂ=>τ*w) 0 := analyticAt_id.mul analyticAt_const
  have hb:AnalyticAt ℂ (fun τ:ℂ=>β (τ*w)) 0 :=
    hβ.comp_of_eq hm (by simp)
  have hA:AnalyticAt ℂ A 0 := ha.comp_of_eq hm (by simp)
  have hF:AnalyticAt ℂ F 0 := analyticAt_const.mul hb
  have hF0:F 0=0 := by simp[F,hβ0]
  change WP.coeff (fun τ:ℂ=>Complex.exp (F τ)*A τ) n=_
  have hExp:AnalyticAt ℂ (fun τ:ℂ=>Complex.exp (F τ)) 0:=hF.cexp
  rw [←taylor_coeff,taylor_mul (f:=fun τ:ℂ=>Complex.exp (F τ)) (g:=A) hExp hA,
    taylor_exp_comp_zero F hF hF0,exp_subst_mul_coeff_finite _ _ (by rw [taylor_constant,hF0])]
  apply Finset.sum_congr rfl
  intro j hj
  rw [←taylor_pow hF j,←taylor_mul (f:=fun τ:ℂ=>F τ^j) (g:=A) (hF.pow j) hA,taylor_coeff]
  have he:(fun τ:ℂ=>F τ^j*A τ)=
      (fun τ:ℂ=>w^(2*j)*(β (τ*w)^j*a (τ*w))) := by
    funext τ
    dsimp only[F,A]
    rw [mul_pow,pow_mul]
    ring
  rw [he]
  have hc:=congrArg (PowerSeries.coeff n)
    (taylor_const_mul (w^(2*j)) (fun τ:ℂ=>β (τ*w)^j*a (τ*w)))
  simp only [taylor_coeff,PowerSeries.coeff_C_mul] at hc
  rw [hc]
  change w^(2*j)*WP.coeff (fun τ:ℂ=>(fun z:ℂ=>β z^j*a z) (τ*w)) n/(j.factorial:ℂ)=_
  rw [coeff_complex_scale_right (fun z:ℂ=>β z^j*a z) w n,pow_add]
  ring
def stationaryTaylorPolynomial (β a:ℂ → ℂ) (n:ℕ):Polynomial ℂ :=
  ∑j ∈ Finset.range (n+1),Polynomial.monomial (n+2*j)
    (WP.coeff (fun z:ℂ=>β z^j*a z) n/(j.factorial:ℂ))
lemma stationaryTaylorPolynomial_eval (β a:ℂ → ℂ) (hβ:AnalyticAt ℂ β 0)
    (ha:AnalyticAt ℂ a 0) (hβ0:β 0=0) (w:ℂ) (n:ℕ) :
    (stationaryTaylorPolynomial β a n).eval w=
      WP.coeff (fun τ:ℂ=>Complex.exp (w^2*β (τ*w))*a (τ*w)) n := by
  rw [stationary_taylor_coefficient_formula β a hβ ha hβ0]
  simp only [stationaryTaylorPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j hj
  ring

def stationaryGaussianCoefficient (β a:ℂ → ℂ) (N:ℕ):ℂ :=
  ∑j ∈ Finset.range (2*N+1),(Nat.doubleFactorial (2*(N+j)-1):ℂ)*
    WP.coeff (fun z:ℂ=>β z^j*a z) (2*N)/(j.factorial:ℂ)
lemma gaussian_standard_even_moment (N:ℕ):
    (∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) • (w:ℂ)^(2*N))=
      (Real.sqrt (2*Real.pi):ℂ)*(Nat.doubleFactorial (2*N-1):ℂ) := by
  have he:=gaussian_complex_even_moment 1 (by norm_num) N
  norm_num only [Real.sqrt_one,Complex.ofReal_one,one_mul,one_pow,div_one] at he
  push_cast at he
  exact he
lemma stationary_taylor_even_gaussian_moment (β a:ℂ → ℂ) (hβ:AnalyticAt ℂ β 0)
    (ha:AnalyticAt ℂ a 0) (hβ0:β 0=0) (N:ℕ) :
    (∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) •
      WP.coeff (fun τ:ℂ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ)))*a (τ*(w:ℂ))) (2*N))=
      (Real.sqrt (2*Real.pi):ℂ)*stationaryGaussianCoefficient β a N := by
  let c:ℕ → ℂ:=fun j=>WP.coeff (fun z:ℂ=>β z^j*a z) (2*N)/(j.factorial:ℂ)
  have he:(fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2) •
        WP.coeff (fun τ:ℂ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ)))*a (τ*(w:ℂ))) (2*N))=
      (fun w:ℝ=>∑j ∈ Finset.range (2*N+1),c j*(Real.exp (-(1/2:ℝ)*w^2) • (w:ℂ)^(2*(N+j)))) := by
    funext w
    rw [stationary_taylor_coefficient_formula β a hβ ha hβ0,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show 2*N+2*j=2*(N+j) by omega]
    change (Real.exp (-(1/2:ℝ)*w^2):ℂ)*((w:ℂ)^(2*(N+j))*WP.coeff (fun z:ℂ=>β z^j*a z) (2*N)/(j.factorial:ℂ))=_
    dsimp only [c]
    simp only [Complex.real_smul]
    ring
  rw [he,MeasureTheory.integral_finsetSum]
  · simp only [MeasureTheory.integral_const_mul,gaussian_standard_even_moment]
    unfold stationaryGaussianCoefficient
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [c]
    ring
  · intro j hj
    exact (gaussian_complex_monomial_integrable (1/2) (by norm_num) (2*(N+j))).const_mul (c j)
end WP.Analysis
