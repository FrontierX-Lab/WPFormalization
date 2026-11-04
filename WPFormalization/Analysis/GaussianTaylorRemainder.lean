import WPFormalization.Analysis.UniformTaylorRemainder
import WPFormalization.Analysis.FiniteWatson
import WPFormalization.Analysis.GaussianFactorialMoments
/-! Exact real and complex Gaussian polynomial moments and simultaneous Taylor
remainder integration on one fixed Cauchy disk. The bounds hold at every
truncation order; no order-dependent analytic neighborhood is assumed. -/
noncomputable section
open MeasureTheory Set
namespace WP.Analysis
lemma gaussian_even_moment_gamma (a:ℝ) (ha:0<a) (N:ℕ) :
    (∫x:ℝ,x^(2*N)*Real.exp (-a*x^2))=
      (1/a)^((N:ℝ)+1/2)*Real.Gamma ((N:ℝ)+1/2) := by
  let f:ℝ→ℝ := fun x=>x^(2*N)*Real.exp (-a*x^2)
  let g:ℝ→ℝ := fun t=>t^((N:ℝ)+1/2-1)*Real.exp (-a*t)
  have hp (x:ℝ) (hx:0<x) : x*(x^2)^((N:ℝ)+1/2-1)=x^(2*N) := by
    calc _ = x^(1:ℝ)*x^((2:ℝ)*((N:ℝ)+1/2-1)) := by
                rw [Real.rpow_one,←Real.rpow_two,←Real.rpow_mul hx.le]
         _ = x^((1:ℝ)+2*((N:ℝ)+1/2-1)) := (Real.rpow_add hx 1 (2*((N:ℝ)+1/2-1))).symm
         _ = x^((2*N:ℕ):ℝ) := by congr 1;push_cast;ring
         _ = _ := Real.rpow_natCast x _
  have hsub := integral_comp_rpow_Ioi_of_pos (g:=g) (show (0:ℝ)<2 by norm_num)
  have hlhs : (∫x:ℝ in Ioi 0,(2*x^((2:ℝ)-1)) • g (x^(2:ℝ)))=2*(∫x:ℝ in Ioi 0,f x) := by
    calc _ = ∫x:ℝ in Ioi 0,2*f x := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x hx
              dsimp only [g,f]
              simp only [smul_eq_mul,show (2:ℝ)-1=1 by norm_num,Real.rpow_one,Real.rpow_two]
              rw [mul_assoc,←mul_assoc x,hp x hx]
         _ = _ := integral_const_mul _ _
  rw [hlhs] at hsub
  have hgam := Real.integral_rpow_mul_exp_neg_mul_Ioi (show 0<(N:ℝ)+1/2 by positivity) ha
  have hgam' : (∫t:ℝ in Ioi 0,g t)=(1/a)^((N:ℝ)+1/2)*Real.Gamma ((N:ℝ)+1/2) := by
    simpa only [g,neg_mul] using hgam
  rw [hgam'] at hsub
  have hi:Integrable f := by
    simpa only [f,Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq ha (s:=((2*N:ℕ):ℝ)) (by
        have h : (0:ℝ)≤(2*N:ℕ) := by positivity
        linarith))
  have hhalf : (∫x:ℝ in Iic 0,f x)=(∫x:ℝ in Ioi 0,f x) := by
    calc _ = ∫x:ℝ in Ioi 0,f (-x) := by simpa using (integral_comp_neg_Ioi 0 f).symm
         _ = _ := by
           apply setIntegral_congr_fun measurableSet_Ioi
           intro x hx
           simp [f,neg_pow,show Even (2*N) from even_two_mul N]
  change (∫x:ℝ,f x)=_
  rw [←integral_add_compl (s:=Ioi (0:ℝ)) measurableSet_Ioi hi,compl_Ioi,hhalf,←two_mul]
  exact hsub
end WP.Analysis

namespace WP.Analysis
lemma gaussian_even_power_integrable (a:ℝ) (ha:0<a) (N:ℕ) :
    Integrable (fun x:ℝ=>x^(2*N)*Real.exp (-a*x^2)) := by
  simpa only [Real.rpow_natCast] using
    (integrable_rpow_mul_exp_neg_mul_sq ha (s:=((2*N:ℕ):ℝ))
      (by
        have h : (0:ℝ)≤(2*N:ℕ) := by positivity
        linarith))

lemma gaussian_even_moment_factorial_bound (a:ℝ) (ha:0<a) (N:ℕ) :
    (∫x:ℝ,x^(2*N)*Real.exp (-a*x^2))≤
      (N.factorial:ℝ)*(2/a)^N*Real.sqrt (2*Real.pi/a) := by
  have hi:=gaussian_even_power_integrable a ha N
  have hg : Integrable (fun x:ℝ=>(N.factorial:ℝ)*(2/a)^N*Real.exp (-(a/2)*x^2)) :=
    (integrable_exp_neg_mul_sq (half_pos ha)).const_mul _
  have hm:=integral_mono hi hg (gaussian_factorial_point_bound a · ha N)
  rw [integral_const_mul,integral_gaussian] at hm
  have he : Real.pi/(a/2)=2*Real.pi/a := by ring
  simpa only [he] using hm

lemma gaussian_local_taylor_remainder_bound (f:ℂ→ℂ) (R M r a:ℝ)
    (hR:0<R) (hM:0≤M) (hr:0<r) (hrR:r≤R/2) (ha:0<a)
    (hf:DifferentiableOn ℂ f (Metric.closedBall 0 R))
    (hbound:∀z∈Metric.sphere (0:ℂ) R,‖f z‖≤M) (N:ℕ) :
    ‖∫x:ℝ in Icc (-r) r, Real.exp (-a*x^2) •
      (f (x:ℂ)-∑m∈Finset.range (2*N),WP.coeff f m*(x:ℂ)^m)‖≤
      (2*M/R^(2*N))*((N.factorial:ℝ)*(2/a)^N*Real.sqrt (2*Real.pi/a)) := by
  let K:ℝ := 2*M/R^(2*N)
  let g:ℝ→ℝ := fun x=>K*(x^(2*N)*Real.exp (-a*x^2))
  have hK:0≤K := by dsimp [K];positivity
  have hg:Integrable g := (gaussian_even_power_integrable a ha N).const_mul K
  have hnonneg (x:ℝ):0≤g x := by
    dsimp only [g]
    rw [pow_mul]
    positivity
  have hp (x:ℝ) (hx:x∈Icc (-r) r) :
      ‖Real.exp (-a*x^2) • (f (x:ℂ)-∑m∈Finset.range (2*N),WP.coeff f m*(x:ℂ)^m)‖≤g x := by
    have hxn : |x|≤r := abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
    have hxc : ‖(x:ℂ)‖≤R/2 := by
      rw [Complex.norm_real,Real.norm_eq_abs]
      exact hxn.trans hrR
    have ht:=complex_taylor_remainder_bound f R M hR hM hf hbound (2*N) (x:ℂ) hxc
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc _ ≤ Real.exp (-a*x^2)*(2*M*(‖(x:ℂ)‖/R)^(2*N)) :=
            mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
         _ = g x := by
            dsimp only [g,K]
            rw [Complex.norm_real,Real.norm_eq_abs,div_pow]
            have he : |x|^(2*N)=x^(2*N) := by rw [pow_mul,pow_mul,sq_abs]
            rw [he]
            ring
  have hb := norm_integral_le_of_norm_le hg.integrableOn
    (ae_restrict_of_forall_mem measurableSet_Icc hp)
  have hs : (∫x:ℝ in Icc (-r) r,g x)≤∫x:ℝ,g x :=
    setIntegral_le_integral hg (Filter.Eventually.of_forall hnonneg)
  calc _ ≤ ∫x:ℝ in Icc (-r) r,g x := hb
       _ ≤ ∫x:ℝ,g x := hs
       _ = K*(∫x:ℝ,x^(2*N)*Real.exp (-a*x^2)) := integral_const_mul _ _
       _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_even_moment_factorial_bound a ha N) hK
end WP.Analysis

namespace WP.Analysis
lemma gaussian_even_moment_doubleFactorial (a:ℝ) (ha:0<a) (N:ℕ) :
    (∫x:ℝ,x^(2*N)*Real.exp (-a*x^2))=
      (Nat.doubleFactorial (2*N-1):ℝ)*Real.sqrt (Real.pi/a)/(2*a)^N := by
  rw [gaussian_even_moment_gamma a ha N,Real.Gamma_nat_add_half,
    Real.rpow_add (div_pos (by norm_num : (0:ℝ)<1) ha),Real.rpow_natCast,←Real.sqrt_eq_rpow]
  have hs : Real.sqrt (1/a)*Real.sqrt Real.pi=Real.sqrt (Real.pi/a) := by
    rw [←Real.sqrt_mul (by positivity : (0:ℝ)≤1/a)]
    congr 1
    ring
  calc _ = (Nat.doubleFactorial (2*N-1):ℝ)*(Real.sqrt (1/a)*Real.sqrt Real.pi)/(2*a)^N := by
              rw [mul_pow,div_pow]
              field_simp
              <;> ring
       _ = _ := by rw [hs]

lemma gaussian_normalized_even_moment (h:ℝ) (hh:0<h) (N:ℕ) :
    Real.sqrt h*(∫x:ℝ,x^(2*N)*Real.exp (-(h/2)*x^2))=
      Real.sqrt (2*Real.pi)*(Nat.doubleFactorial (2*N-1):ℝ)/h^N := by
  rw [gaussian_even_moment_doubleFactorial (h/2) (half_pos hh) N,show 2*(h/2)=h by ring]
  have hs : Real.sqrt h*Real.sqrt (Real.pi/(h/2))=Real.sqrt (2*Real.pi) := by
    rw [←Real.sqrt_mul hh.le]
    congr 1
    field_simp
    <;> ring
  calc _ = (Real.sqrt h*Real.sqrt (Real.pi/(h/2)))*(Nat.doubleFactorial (2*N-1):ℝ)/h^N := by ring
       _ = _ := by rw [hs]

lemma gaussian_odd_moment_zero (a:ℝ) (N:ℕ) :
    (∫x:ℝ,x^(2*N+1)*Real.exp (-a*x^2))=0 := by
  let f:ℝ→ℝ := fun x=>x^(2*N+1)*Real.exp (-a*x^2)
  have ho (x:ℝ):f (-x)=-f x := by
    dsimp only [f]
    simp [neg_pow,pow_add,pow_mul]
  have he : (∫x:ℝ,f (-x))=∫x:ℝ,f x := integral_neg_eq_self f volume
  simp_rw [ho] at he
  rw [integral_neg] at he
  change (∫x:ℝ,f x)=0
  linarith
end WP.Analysis

namespace WP.Analysis
lemma gaussian_monomial_integrable (a:ℝ) (ha:0<a) (m:ℕ) :
    Integrable (fun x:ℝ=>x^m*Real.exp (-a*x^2)) := by
  simpa only [Real.rpow_natCast] using
    (integrable_rpow_mul_exp_neg_mul_sq ha (s:=(m:ℝ)) (by
      have hm:(0:ℝ)≤(m:ℝ) := Nat.cast_nonneg m
      linarith))

lemma gaussian_complex_monomial_integrable (a:ℝ) (ha:0<a) (m:ℕ) :
    Integrable (fun x:ℝ=>Real.exp (-a*x^2) • (x:ℂ)^m) := by
  have hi : Integrable (fun x:ℝ=>((x^m*Real.exp (-a*x^2):ℝ):ℂ)) := (gaussian_monomial_integrable a ha m).ofReal
  convert! hi using 1
  funext x
  change (Real.exp (-a*x^2):ℂ)*(x:ℂ)^m=((x^m*Real.exp (-a*x^2):ℝ):ℂ)
  push_cast
  ring

lemma gaussian_complex_even_moment (h:ℝ) (hh:0<h) (N:ℕ) :
    (Real.sqrt h:ℂ)*(∫x:ℝ,Real.exp (-(h/2)*x^2) • (x:ℂ)^(2*N))=
      ((Real.sqrt (2*Real.pi)*(Nat.doubleFactorial (2*N-1):ℝ)/h^N:ℝ):ℂ) := by
  have he:(fun x:ℝ=>Real.exp (-(h/2)*x^2) • (x:ℂ)^(2*N))=
      (fun x:ℝ=>((x^(2*N)*Real.exp (-(h/2)*x^2):ℝ):ℂ)) := by
    funext x
    change (Real.exp (-(h/2)*x^2):ℂ)*(x:ℂ)^(2*N)=_
    push_cast
    ring
  rw [he,integral_complex_ofReal,←Complex.ofReal_mul]
  exact congrArg (fun x:ℝ=>(x:ℂ)) (gaussian_normalized_even_moment h hh N)

lemma gaussian_complex_odd_moment (a:ℝ) (N:ℕ) :
    (∫x:ℝ,Real.exp (-a*x^2) • (x:ℂ)^(2*N+1))=0 := by
  have he:(fun x:ℝ=>Real.exp (-a*x^2) • (x:ℂ)^(2*N+1))=
      (fun x:ℝ=>((x^(2*N+1)*Real.exp (-a*x^2):ℝ):ℂ)) := by
    funext x
    change (Real.exp (-a*x^2):ℂ)*(x:ℂ)^(2*N+1)=_
    push_cast
    ring
  rw [he,integral_complex_ofReal,gaussian_odd_moment_zero,Complex.ofReal_zero]
end WP.Analysis

namespace WP.Analysis
lemma gaussian_sum_range_pairs {E:Type*} [AddCommMonoid E] (f:ℕ→E) (N:ℕ) :
    (∑m∈Finset.range (2*N),f m)=∑a∈Finset.range N,(f (2*a)+f (2*a+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)=2*N+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,
      Finset.sum_range_succ,ih]
    ac_rfl

lemma gaussian_polynomial_exact (h:ℝ) (hh:0<h) (N:ℕ) (c:ℕ→ℂ) :
    (Real.sqrt h:ℂ)*(∫x:ℝ,Real.exp (-(h/2)*x^2) •
      (∑m∈Finset.range (2*N),c m*(x:ℂ)^m))=
      (Real.sqrt (2*Real.pi):ℂ)*
        (∑a∈Finset.range N,c (2*a)*(Nat.doubleFactorial (2*a-1):ℂ)/(h:ℂ)^a) := by
  have heq : (fun x:ℝ=>Real.exp (-(h/2)*x^2) •
      (∑m∈Finset.range (2*N),c m*(x:ℂ)^m))=
      (fun x:ℝ=>∑m∈Finset.range (2*N),c m*(Real.exp (-(h/2)*x^2) • (x:ℂ)^m)) := by
    funext x
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    change (Real.exp (-(h/2)*x^2):ℂ)*(c m*(x:ℂ)^m)=c m*((Real.exp (-(h/2)*x^2):ℂ)*(x:ℂ)^m)
    ring
  rw [heq,integral_finset_sum]
  · simp_rw [integral_const_mul]
    rw [Finset.mul_sum,gaussian_sum_range_pairs]
    simp only [gaussian_complex_odd_moment,mul_zero,add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    calc _ = c (2*a)*((Real.sqrt h:ℂ)*(∫x:ℝ,Real.exp (-(h/2)*x^2) • (x:ℂ)^(2*a))) := by ring
         _ = c (2*a)*((Real.sqrt (2*Real.pi)*(Nat.doubleFactorial (2*a-1):ℝ)/h^a:ℝ):ℂ) := by
              rw [gaussian_complex_even_moment h hh a]
         _ = _ := by push_cast;ring
  · intro m hm
    exact (gaussian_complex_monomial_integrable (h/2) (half_pos hh) m).const_mul (c m)
end WP.Analysis

namespace WP.Analysis
lemma gaussian_local_taylor_remainder_normalized (f:ℂ→ℂ) (R M r h:ℝ)
    (hR:0<R) (hM:0≤M) (hr:0<r) (hrR:r≤R/2) (hh:0<h)
    (hf:DifferentiableOn ℂ f (Metric.closedBall 0 R))
    (hbound:∀z∈Metric.sphere (0:ℂ) R,‖f z‖≤M) (N:ℕ) :
    Real.sqrt h*‖∫x:ℝ in Icc (-r) r, Real.exp (-(h/2)*x^2) •
      (f (x:ℂ)-∑m∈Finset.range (2*N),WP.coeff f m*(x:ℂ)^m)‖≤
      (2*M*Real.sqrt (4*Real.pi))*(4/R^2)^N*(N.factorial:ℝ)/h^N := by
  have hb:=mul_le_mul_of_nonneg_left
    (gaussian_local_taylor_remainder_bound f R M r (h/2) hR hM hr hrR (half_pos hh) hf hbound N)
    (Real.sqrt_nonneg h)
  have hs : Real.sqrt h*Real.sqrt (2*Real.pi/(h/2))=Real.sqrt (4*Real.pi) := by
    rw [←Real.sqrt_mul hh.le]
    congr 1
    field_simp
    <;> ring
  apply hb.trans_eq
  calc _ = (2*M)*(4/h)^N*(N.factorial:ℝ)/R^(2*N)*
        (Real.sqrt h*Real.sqrt (2*Real.pi/(h/2))) := by
          rw [show 2/(h/2)=4/h by ring]
          ring
       _ = _ := by
          rw [hs,pow_mul,div_pow,div_pow]
          field_simp
          <;> ring
end WP.Analysis
