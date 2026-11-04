import WPFormalization.Analysis.GaussianTaylorRemainder
import WPFormalization.Analysis.GaussianGevreyConvolution
/-! Common-order Taylor errors for finite Gaussian Gevrey-two amplitude families,
together with uniform prefix and moment-factor estimates in the square-root
order window. Every statement is proved from its displayed analytic bounds. -/
noncomputable section
open MeasureTheory Set
namespace WP.Analysis
lemma gaussian_gevrey_two_taylor_family (f:ℕ→ℂ→ℂ) (C B R r h:ℝ)
    (hC:0≤C) (hB:0≤B) (hR:0<R) (hr:0<r) (hrR:r≤R/2) (hh:0<h)
    (hf:∀s,DifferentiableOn ℂ (f s) (Metric.closedBall 0 R))
    (hbound:∀s z,z∈Metric.sphere (0:ℂ) R→‖f s z‖≤C*B^s*(s.factorial:ℝ)^2) (K:ℕ) :
    ‖∑s∈Finset.range (K+1),(Real.sqrt h:ℂ)/(h:ℂ)^s*
      (∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) •
        (f s (x:ℂ)-∑m∈Finset.range (2*(K+1-s)),WP.coeff (f s) m*(x:ℂ)^m))‖≤
      (2*C*Real.sqrt (4*Real.pi))*(2*max B (4/R^2))^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1) := by
  let A:ℝ := 2*C*Real.sqrt (4*Real.pi)
  let D:ℝ := 4/R^2
  let e:ℕ→ℝ := fun s=>B^s*(s.factorial:ℝ)^2*D^(K+1-s)*((K+1-s).factorial:ℝ)
  have hA:0≤A := by dsimp [A];positivity
  have hD:0≤D := by dsimp [D];positivity
  have hterm (s:ℕ) (hs:s∈Finset.range (K+1)) :
      ‖(Real.sqrt h:ℂ)/(h:ℂ)^s*
        (∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) •
          (f s (x:ℂ)-∑m∈Finset.range (2*(K+1-s)),WP.coeff (f s) m*(x:ℂ)^m))‖≤
        A/h^(K+1)*e s := by
    let I:ℂ := ∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) •
      (f s (x:ℂ)-∑m∈Finset.range (2*(K+1-s)),WP.coeff (f s) m*(x:ℂ)^m)
    have hM:0≤C*B^s*(s.factorial:ℝ)^2 := by positivity
    have hb:=gaussian_local_taylor_remainder_normalized (f s) R (C*B^s*(s.factorial:ℝ)^2) r h
      hR hM hr hrR hh (hf s) (hbound s) (K+1-s)
    change Real.sqrt h*‖I‖≤_ at hb
    have hn : ‖(Real.sqrt h:ℂ)/(h:ℂ)^s*I‖=(Real.sqrt h*‖I‖)/h^s := by
      simp only [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hh,abs_of_nonneg (Real.sqrt_nonneg h)]
      ring
    change ‖(Real.sqrt h:ℂ)/(h:ℂ)^s*I‖≤_
    rw [hn]
    apply (div_le_div_of_nonneg_right hb (pow_nonneg hh.le s)).trans_eq
    have hplus:s+(K+1-s)=K+1 := Nat.add_sub_of_le (Finset.mem_range.mp hs).le
    have hp:h^s*h^(K+1-s)=h^(K+1) := by rw [←pow_add,hplus]
    dsimp only [A,e,D]
    rw [div_div,←hp]
    field_simp
    <;> ring
  calc _ ≤ ∑s∈Finset.range (K+1),‖(Real.sqrt h:ℂ)/(h:ℂ)^s*
          (∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) •
            (f s (x:ℂ)-∑m∈Finset.range (2*(K+1-s)),WP.coeff (f s) m*(x:ℂ)^m))‖ := norm_sum_le _ _
       _ ≤ ∑s∈Finset.range (K+1),A/h^(K+1)*e s := Finset.sum_le_sum hterm
       _ = A/h^(K+1)*(∑s∈Finset.range (K+1),e s) := (Finset.mul_sum _ _ _).symm
       _ ≤ A/h^(K+1)*((2*max B D)^(K+1)*((K+1).factorial:ℝ)^2) :=
            mul_le_mul_of_nonneg_left (gaussian_gevrey_two_convolution B D hB hD K) (by positivity)
       _ = _ := by dsimp only [A,D];ring
end WP.Analysis

namespace WP.Analysis
lemma gaussian_gevrey_prefix_bound (B h:ℝ) (hB:0≤B) (hh:0<h) (J:ℕ)
    (hwindow:B*((J:ℝ)+1)^2/h≤1/2) :
    (∑s∈Finset.range (J+1),B^s*(s.factorial:ℝ)^2/h^s)≤2 := by
  have ht:=gaussian_unused_amplitude_tail B h hB hh J 0 hwindow
  simp only [Nat.zero_add,Nat.sub_zero,Nat.factorial_one,Nat.cast_one,pow_one,mul_one] at ht
  rw [Finset.sum_range_succ']
  have hBh:B/h≤1/2 := by
    apply le_trans _ hwindow
    exact div_le_div_of_nonneg_right (by
      have hx:1≤((J:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) J]
      nlinarith) hh.le
  simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,div_one]
  calc _ ≤ 2*B/h+1 := by simpa [Nat.add_comm] using add_le_add_right ht 1
       _ ≤ 2 := by rw [mul_div_assoc];linarith
lemma gaussian_moment_tail_factor_le_one (h:ℝ) (hh:0<h) (N K:ℕ)
    (hNK:N≤K+1) (hwindow:8*((K:ℝ)+1)≤h) :
    (N.factorial:ℝ)*(8/h)^N≤1 := by
  have hfac:(N.factorial:ℝ)≤(N:ℝ)^N := by exact_mod_cast Nat.factorial_le_pow N
  have hNK':(N:ℝ)≤(K:ℝ)+1 := by exact_mod_cast hNK
  have hratio:(8*((K:ℝ)+1))/h≤1 := (div_le_one hh).mpr hwindow
  calc _ ≤ ((K:ℝ)+1)^N*(8/h)^N := mul_le_mul_of_nonneg_right
          (hfac.trans (pow_le_pow_left₀ (Nat.cast_nonneg N) hNK' N)) (by positivity)
       _ = ((8*((K:ℝ)+1))/h)^N := by rw [←mul_pow];congr 1;ring
       _ ≤ 1 := pow_le_one₀ (by positivity) hratio
end WP.Analysis
