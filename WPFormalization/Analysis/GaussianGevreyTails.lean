import WPFormalization.Analysis.GaussianPolynomialTail
import WPFormalization.Analysis.GaussianGevreyFamily
/-! Finite Gaussian amplitude families retain a uniform exponentially small
polynomial-extension tail and a Gevrey-two first-unused-amplitude bound. The
true integrals and all order windows are explicit in each statement. -/
noncomputable section
open MeasureTheory Set
namespace WP.Analysis
lemma gaussian_gevrey_two_polynomial_tail_family (f:ℕ→ℂ→ℂ) (C B R r h:ℝ)
    (hC:0≤C) (hB:0≤B) (hR:0<R) (hr:0<r) (hh:0<h)
    (hf:∀s,DifferentiableOn ℂ (f s) (Metric.closedBall 0 R))
    (hbound:∀s z,z∈Metric.sphere (0:ℂ) R→‖f s z‖≤C*B^s*(s.factorial:ℝ)^2)
    (K:ℕ) (hwindow:B*((K:ℝ)+1)^2/h≤1/2) (hsmall:8*((K:ℝ)+1)≤h) :
    ‖∑s∈Finset.range (K+1),(Real.sqrt h:ℂ)/(h:ℂ)^s*
      (∫x:ℝ in (Icc (-r) r)ᶜ,Real.exp (-(h/2)*x^2) •
        (∑m∈Finset.range (2*(K+1-s)),WP.coeff (f s) m*(x:ℂ)^m))‖≤
      4*C*Real.sqrt (8*Real.pi)*(2*max 1 R⁻¹)^(2*(K+1))*Real.exp (-(h/4)*r^2) := by
  let D:ℝ := 2*max 1 R⁻¹
  let A:ℝ := 2*C*D^(2*(K+1))*Real.exp (-(h/4)*r^2)*Real.sqrt (8*Real.pi)
  let e:ℕ→ℝ := fun s=>B^s*(s.factorial:ℝ)^2/h^s
  have hD:1≤D := by dsimp [D];linarith [le_max_left (1:ℝ) R⁻¹]
  have hA:0≤A := by dsimp [A];positivity
  have hterm (s:ℕ) (hs:s∈Finset.range (K+1)) :
      ‖(Real.sqrt h:ℂ)/(h:ℂ)^s*
        (∫x:ℝ in (Icc (-r) r)ᶜ,Real.exp (-(h/2)*x^2) •
          (∑m∈Finset.range (2*(K+1-s)),WP.coeff (f s) m*(x:ℂ)^m))‖≤A*e s := by
    let M:ℝ := C*B^s*(s.factorial:ℝ)^2
    let N:ℕ := K+1-s
    let I:ℂ := ∫x:ℝ in (Icc (-r) r)ᶜ,Real.exp (-(h/2)*x^2) •
      (∑m∈Finset.range (2*N),WP.coeff (f s) m*(x:ℂ)^m)
    have hM:0≤M := by dsimp [M];positivity
    have hc(m:ℕ):‖WP.coeff (f s) m‖≤M/R^m :=
      coeff_norm_le_circle_bound (f s) R M hR (hf s) (hbound s) m
    have ht:=gaussian_polynomial_outer_tail_bound (WP.coeff (f s)) M R r h hM hR hr hh hc N
    change Real.sqrt h*‖I‖≤M*D^(2*N)*Real.exp (-(h/4)*r^2)*Real.sqrt (8*Real.pi)*
      (1+(N.factorial:ℝ)*(8/h)^N) at ht
    have hfac:=gaussian_moment_tail_factor_le_one h hh N K (Nat.sub_le _ _) hsmall
    have hpow:D^(2*N)≤D^(2*(K+1)) := pow_le_pow_right₀ hD (by dsimp [N];omega)
    have ht':Real.sqrt h*‖I‖≤2*M*D^(2*(K+1))*Real.exp (-(h/4)*r^2)*Real.sqrt (8*Real.pi) := by
      apply ht.trans
      calc _ ≤ M*D^(2*(K+1))*Real.exp (-(h/4)*r^2)*Real.sqrt (8*Real.pi)*2 := by
                  gcongr
                  linarith
           _ = _ := by ring
    have hn:‖(Real.sqrt h:ℂ)/(h:ℂ)^s*I‖=(Real.sqrt h*‖I‖)/h^s := by
      simp only [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hh,abs_of_nonneg (Real.sqrt_nonneg h)]
      ring
    change ‖(Real.sqrt h:ℂ)/(h:ℂ)^s*I‖≤_
    rw [hn]
    apply (div_le_div_of_nonneg_right ht' (pow_nonneg hh.le s)).trans_eq
    dsimp only [M,A,e]
    ring
  calc _ ≤ ∑s∈Finset.range (K+1),‖(Real.sqrt h:ℂ)/(h:ℂ)^s*
          (∫x:ℝ in (Icc (-r) r)ᶜ,Real.exp (-(h/2)*x^2) •
            (∑m∈Finset.range (2*(K+1-s)),WP.coeff (f s) m*(x:ℂ)^m))‖ := norm_sum_le _ _
       _ ≤ ∑s∈Finset.range (K+1),A*e s := Finset.sum_le_sum hterm
       _ = A*(∑s∈Finset.range (K+1),e s) := (Finset.mul_sum _ _ _).symm
       _ ≤ A*2 := mul_le_mul_of_nonneg_left (gaussian_gevrey_prefix_bound B h hB hh K hwindow) hA
       _ = _ := by dsimp only [A,D];ring

lemma gaussian_local_amplitude_bound (f:ℂ→ℂ) (M r h:ℝ) (hM:0≤M) (hh:0<h)
    (hbound:∀x∈Icc (-r) r,‖f (x:ℂ)‖≤M) :
    Real.sqrt h*‖∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) • f (x:ℂ)‖≤
      M*Real.sqrt (2*Real.pi) := by
  let g:ℝ→ℝ := fun x=>M*Real.exp (-(h/2)*x^2)
  have hg:Integrable g := (integrable_exp_neg_mul_sq (half_pos hh)).const_mul M
  have hp (x:ℝ) (hx:x∈Icc (-r) r) :
      ‖Real.exp (-(h/2)*x^2) • f (x:ℂ)‖≤g x := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hbound x hx) (Real.exp_pos _).le).trans_eq (by dsimp only [g];ring)
  have hb:=norm_integral_le_of_norm_le hg.integrableOn (ae_restrict_of_forall_mem measurableSet_Icc hp)
  have hs : (∫x:ℝ in Icc (-r) r,g x)≤∫x:ℝ,g x :=
    setIntegral_le_integral hg (Filter.Eventually.of_forall (fun x=>by dsimp only [g];positivity))
  have he : Real.sqrt h*(∫x:ℝ,Real.exp (-(h/2)*x^2))=Real.sqrt (2*Real.pi) := by
    simpa using gaussian_normalized_even_moment h hh 0
  calc _ ≤ Real.sqrt h*(∫x:ℝ,g x) := mul_le_mul_of_nonneg_left (hb.trans hs) (Real.sqrt_nonneg h)
       _ = M*(Real.sqrt h*(∫x:ℝ,Real.exp (-(h/2)*x^2))) := by rw [integral_const_mul];ring
       _ = _ := by rw [he]

lemma gaussian_gevrey_two_unused_amplitude_family (f:ℕ→ℂ→ℂ) (C B r h:ℝ)
    (hC:0≤C) (hB:0≤B) (hh:0<h)
    (hbound:∀s x,x∈Icc (-r) r→‖f s (x:ℂ)‖≤C*B^s*(s.factorial:ℝ)^2)
    (J K:ℕ) (hwindow:B*((J:ℝ)+1)^2/h≤1/2) :
    ‖∑n∈Finset.range (J-K),(Real.sqrt h:ℂ)/(h:ℂ)^(K+1+n)*
      (∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) • f (K+1+n) (x:ℂ))‖≤
      2*C*Real.sqrt (2*Real.pi)*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1) := by
  let A:ℝ := C*Real.sqrt (2*Real.pi)
  have hA:0≤A := by dsimp [A];positivity
  have hterm(n:ℕ):
      ‖(Real.sqrt h:ℂ)/(h:ℂ)^(K+1+n)*
        (∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) • f (K+1+n) (x:ℂ))‖≤
        A*(B^(K+1+n)*((K+1+n).factorial:ℝ)^2/h^(K+1+n)) := by
    have hb:=gaussian_local_amplitude_bound (f (K+1+n))
      (C*B^(K+1+n)*((K+1+n).factorial:ℝ)^2) r h (by positivity) hh (hbound (K+1+n))
    let I:ℂ := ∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) • f (K+1+n) (x:ℂ)
    change Real.sqrt h*‖I‖≤_ at hb
    change ‖(Real.sqrt h:ℂ)/(h:ℂ)^(K+1+n)*I‖≤_
    have hn:‖(Real.sqrt h:ℂ)/(h:ℂ)^(K+1+n)*I‖=(Real.sqrt h*‖I‖)/h^(K+1+n) := by
      simp only [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hh,abs_of_nonneg (Real.sqrt_nonneg h)]
      ring
    rw [hn]
    exact (div_le_div_of_nonneg_right hb (by positivity)).trans_eq (by dsimp only [A];ring)
  calc _ ≤ ∑n∈Finset.range (J-K),‖(Real.sqrt h:ℂ)/(h:ℂ)^(K+1+n)*
          (∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) • f (K+1+n) (x:ℂ))‖ := norm_sum_le _ _
       _ ≤ ∑n∈Finset.range (J-K),A*(B^(K+1+n)*((K+1+n).factorial:ℝ)^2/h^(K+1+n)) :=
          Finset.sum_le_sum (fun n hn=>hterm n)
       _ = A*(∑n∈Finset.range (J-K),B^(K+1+n)*((K+1+n).factorial:ℝ)^2/h^(K+1+n)) := (Finset.mul_sum _ _ _).symm
       _ ≤ A*(2*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)) :=
          mul_le_mul_of_nonneg_left (gaussian_unused_amplitude_tail B h hB hh J K hwindow) hA
       _ = _ := by dsimp only [A];ring
end WP.Analysis
