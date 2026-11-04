import WPFormalization.Analysis.GaussianTaylorRemainder

/-! Explicit tails of retained Gaussian Taylor polynomials. Uniform coefficient
bounds on a fixed circle produce a geometric order factor and an exponentially
small spatial tail, with the finite Gaussian-moment factor retained exactly. -/
noncomputable section
open MeasureTheory Set
namespace WP.Analysis
lemma gaussian_finite_polynomial_norm_bound (c:ℕ→ℂ) (M R:ℝ)
    (hM:0≤M) (hR:0<R) (hc:∀m,‖c m‖≤M/R^m) (N:ℕ) (x:ℝ) :
    ‖∑m∈Finset.range (2*N),c m*(x:ℂ)^m‖≤
      M*(2*max 1 R⁻¹)^(2*N)*(1+x^(2*N)) := by
  let D:ℝ := max 1 R⁻¹
  have hD:1≤D := le_max_left _ _
  have hDp:0<D := zero_lt_one.trans_le hD
  have hxp:0≤x^(2*N) := by rw [pow_mul];positivity
  have hpx (m:ℕ) (hm:m≤2*N) : |x|^m≤1+x^(2*N) := by
    have he : |x|^(2*N)=x^(2*N) := by rw [pow_mul,pow_mul,sq_abs]
    by_cases hx:|x|≤1
    · exact (pow_le_one₀ (abs_nonneg x) hx).trans (by linarith)
    · have hp:=pow_le_pow_right₀ (le_of_not_ge hx) hm
      rw [he] at hp
      linarith
  have hcm (m:ℕ) (hm:m≤2*N) : ‖c m‖≤M*D^(2*N) := by
    calc _ ≤ M/R^m := hc m
         _ = M*(R⁻¹)^m := by rw [inv_pow];ring
         _ ≤ M*D^(2*N) := mul_le_mul_of_nonneg_left
            ((pow_le_pow_left₀ (inv_nonneg.mpr hR.le) (le_max_right 1 R⁻¹) m).trans
              (pow_le_pow_right₀ hD hm)) hM
  have hterm (m:ℕ) (hm:m∈Finset.range (2*N)) :
      ‖c m*(x:ℂ)^m‖≤M*D^(2*N)*(1+x^(2*N)) := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (hcm m (Finset.mem_range.mp hm).le)
      (hpx m (Finset.mem_range.mp hm).le) (pow_nonneg (abs_nonneg x) m) (by positivity)
  calc _ ≤ ∑m∈Finset.range (2*N),‖c m*(x:ℂ)^m‖ := norm_sum_le _ _
       _ ≤ ∑_m∈Finset.range (2*N),M*D^(2*N)*(1+x^(2*N)) := Finset.sum_le_sum hterm
       _ = (2*N:ℕ)*(M*D^(2*N)*(1+x^(2*N))) := by simp
       _ ≤ (2:ℝ)^(2*N)*(M*D^(2*N)*(1+x^(2*N))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n:=2*N)))
       _ = _ := by rw [mul_pow];dsimp only [D];ring

lemma gaussian_polynomial_outer_tail_bound (c:ℕ→ℂ) (M R r h:ℝ)
    (hM:0≤M) (hR:0<R) (hr:0<r) (hh:0<h)
    (hc:∀m,‖c m‖≤M/R^m) (N:ℕ) :
    Real.sqrt h*‖∫x:ℝ in (Icc (-r) r)ᶜ, Real.exp (-(h/2)*x^2) •
      (∑m∈Finset.range (2*N),c m*(x:ℂ)^m)‖≤
      M*(2*max 1 R⁻¹)^(2*N)*Real.exp (-(h/4)*r^2)*Real.sqrt (8*Real.pi)*
        (1+(N.factorial:ℝ)*(8/h)^N) := by
  let A:ℝ := M*(2*max 1 R⁻¹)^(2*N)*Real.exp (-(h/4)*r^2)
  let g:ℝ→ℝ := fun x=>A*((1+x^(2*N))*Real.exp (-(h/4)*x^2))
  have hA:0≤A := by dsimp [A];positivity
  have hgi:Integrable (fun x:ℝ=>(1+x^(2*N))*Real.exp (-(h/4)*x^2)) := by
    convert! (integrable_exp_neg_mul_sq (by linarith : 0<h/4)).add
      (gaussian_even_power_integrable (h/4) (by linarith) N) using 1
    funext x
    simp only [Pi.add_apply]
    ring
  have hg:Integrable g := hgi.const_mul A
  have hgn (x:ℝ):0≤g x := by
    dsimp only [g]
    rw [pow_mul]
    positivity
  have hpoint (x:ℝ) (hx:x∈(Icc (-r) r)ᶜ) :
      ‖Real.exp (-(h/2)*x^2) • (∑m∈Finset.range (2*N),c m*(x:ℂ)^m)‖≤g x := by
    have hxr:r≤|x| := by
      by_contra hn
      have habs:|x|<r := lt_of_not_ge hn
      exact hx ⟨(abs_lt.mp habs).1.le,(abs_lt.mp habs).2.le⟩
    have hs : r^2≤x^2 := by nlinarith [sq_abs x,abs_nonneg x]
    have hexp : Real.exp (-(h/2)*x^2)≤Real.exp (-(h/4)*r^2)*Real.exp (-(h/4)*x^2) := by
      rw [←Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc _ ≤ (Real.exp (-(h/4)*r^2)*Real.exp (-(h/4)*x^2))*
          (M*(2*max 1 R⁻¹)^(2*N)*(1+x^(2*N))) := by
            apply mul_le_mul hexp (gaussian_finite_polynomial_norm_bound c M R hM hR hc N x)
              (norm_nonneg _) (by positivity)
         _ = g x := by dsimp only [g,A];ring
  have hb:=norm_integral_le_of_norm_le hg.integrableOn
    (ae_restrict_of_forall_mem measurableSet_Icc.compl hpoint)
  have hs : (∫x:ℝ in (Icc (-r) r)ᶜ,g x)≤∫x:ℝ,g x :=
    setIntegral_le_integral hg (Filter.Eventually.of_forall hgn)
  have hG : (∫x:ℝ,(1+x^(2*N))*Real.exp (-(h/4)*x^2))≤
      (1+(N.factorial:ℝ)*(8/h)^N)*Real.sqrt (8*Real.pi/h) := by
    simp only [add_mul,one_mul]
    rw [integral_add (integrable_exp_neg_mul_sq (by linarith))
      (gaussian_even_power_integrable (h/4) (by linarith) N)]
    have h0:=gaussian_even_moment_factorial_bound (h/4) (by linarith) 0
    simp only [Nat.mul_zero,pow_zero,one_mul,Nat.factorial_zero,Nat.cast_one] at h0
    have hN:=gaussian_even_moment_factorial_bound (h/4) (by linarith) N
    have he:2/(h/4)=8/h := by ring
    have he':2*Real.pi/(h/4)=8*Real.pi/h := by ring
    rw [he'] at h0
    rw [he,he'] at hN
    exact (add_le_add h0 hN).trans_eq (by ring)
  have hroot : Real.sqrt h*Real.sqrt (8*Real.pi/h)=Real.sqrt (8*Real.pi) := by
    rw [←Real.sqrt_mul hh.le]
    congr 1
    field_simp
  calc _ ≤ Real.sqrt h*(∫x:ℝ,g x) :=
          mul_le_mul_of_nonneg_left (hb.trans hs) (Real.sqrt_nonneg h)
       _ = A*(Real.sqrt h*(∫x:ℝ,(1+x^(2*N))*Real.exp (-(h/4)*x^2))) := by
          rw [integral_const_mul]
          ring
       _ ≤ A*(Real.sqrt h*((1+(N.factorial:ℝ)*(8/h)^N)*Real.sqrt (8*Real.pi/h))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG (Real.sqrt_nonneg h)) hA
       _ = _ := by rw [mul_left_comm (Real.sqrt h),hroot];dsimp only [A];ring
end WP.Analysis
