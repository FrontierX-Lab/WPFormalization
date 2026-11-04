import WPFormalization.HigherOrder.Extraction
import WPFormalization.Analysis.GaussianTaylorRemainder
/-! The original prescribed CG3 Gaussian functional is exactly a genuine real Gaussian integral after evaluation on the imaginary axis. The proof retains the negative even-moment signs and vanishing odd moments; no replacement coefficient family is introduced. -/
noncomputable section
open MeasureTheory
namespace WP.Analysis
lemma gaussian_doubleFactorial_eq_odd_product (N:ℕ) :
    (Nat.doubleFactorial (2*N-1):ℝ)=∏i ∈ Finset.range N,(2*(i:ℝ)+1) := by
  induction N with
  | zero=>simp
  | succ N ih=>
    rw [show 2*(N+1)-1=2*N+1 by omega,Nat.doubleFactorial_add_one,Finset.prod_range_succ]
    push_cast
    rw [ih]
    ring
lemma imaginary_gaussian_monomial_moment (n:ℕ) :
    (Complex.I^n)*(∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) • (w:ℂ)^n)=
      (Real.sqrt (2*Real.pi):ℂ)*(HigherOrder.gaussianMoment n:ℂ) := by
  rcases Nat.even_or_odd n with ⟨N,rfl⟩|⟨N,rfl⟩
  · have he:=gaussian_complex_even_moment 1 (by norm_num) N
    norm_num only [Real.sqrt_one,Complex.ofReal_one,one_mul,one_pow,div_one] at he
    have hn:N+N=2*N := by omega
    rw [hn,he,pow_mul,Complex.I_sq]
    simp only [HigherOrder.gaussianMoment,even_two_mul,ite_true,Nat.mul_div_cancel_left _ (by norm_num:0<2)]
    rw [gaussian_doubleFactorial_eq_odd_product]
    push_cast
    ring
  · rw [show 2*N+1=2*N+1 from rfl,gaussian_complex_odd_moment]
    simp [HigherOrder.gaussianMoment]
lemma imaginary_gaussian_polynomial_integrable (p:Polynomial ℝ) :
    Integrable (fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2) •
      (p.map Complex.ofRealHom).eval (Complex.I*(w:ℂ))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>
    convert! hp.add hq using 1
    funext w
    simp only [Polynomial.map_add,Polynomial.eval_add,smul_add,Pi.add_apply]
  | monomial n a=>
    have hi:Integrable (fun w:ℝ=>(a:ℂ)*Complex.I^n*
        (Real.exp (-(1/2:ℝ)*w^2) • (w:ℂ)^n)) :=
      (gaussian_complex_monomial_integrable (1/2) (by norm_num) n).const_mul ((a:ℂ)*Complex.I^n)
    convert! hi using 1
    funext w
    simp only [Polynomial.map_monomial,Polynomial.eval_monomial,mul_pow,Complex.ofRealHom_eq_coe,
      Complex.real_smul]
    ring
lemma gaussianFunctional_integral_realization (p:Polynomial ℝ) :
    (∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) •
      (p.map Complex.ofRealHom).eval (Complex.I*(w:ℂ)))=
      (Real.sqrt (2*Real.pi):ℂ)*(HigherOrder.gaussianFunctional p:ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>
    simp only [Polynomial.map_add,Polynomial.eval_add,smul_add]
    rw [integral_add (imaginary_gaussian_polynomial_integrable p) (imaginary_gaussian_polynomial_integrable q),hp,hq]
    have hGF:HigherOrder.gaussianFunctional (p+q)=HigherOrder.gaussianFunctional p+HigherOrder.gaussianFunctional q := by
      unfold HigherOrder.gaussianFunctional
      exact Polynomial.sum_add_index p q _ (by simp) (by intros;ring)
    rw [hGF,Complex.ofReal_add,mul_add]
  | monomial n a=>
    have he:(fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2) •
        ((Polynomial.monomial n a).map Complex.ofRealHom).eval (Complex.I*(w:ℂ)))=
        (fun w:ℝ=>(a:ℂ)*Complex.I^n*(Real.exp (-(1/2:ℝ)*w^2) • (w:ℂ)^n)) := by
      funext w
      simp only [Polynomial.map_monomial,Polynomial.eval_monomial,mul_pow,Complex.ofRealHom_eq_coe,Complex.real_smul]
      ring
    rw [he,integral_const_mul,mul_assoc,imaginary_gaussian_monomial_moment]
    have hGF:HigherOrder.gaussianFunctional (Polynomial.monomial n a)=a*HigherOrder.gaussianMoment n := by
      unfold HigherOrder.gaussianFunctional
      exact Polynomial.sum_monomial_index a _ (by simp)
    rw [hGF,Complex.ofReal_mul]
    ring
end WP.Analysis
