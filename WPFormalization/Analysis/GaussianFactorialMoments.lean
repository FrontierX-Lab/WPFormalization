import Mathlib
/-! Factorial bounds for every even Gaussian moment, with no relation between order and variance scale. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory
lemma gaussian_factorial_point_bound (a x : ℝ) (ha : 0 < a) (N : ℕ) :
    x^(2*N)*Real.exp (-a*x^2) ≤
      (N.factorial:ℝ)*(2/a)^N*Real.exp (-(a/2)*x^2) := by
  have hfact : 0 < (N.factorial:ℝ) := by positivity
  have hp := (div_le_iff₀ hfact).mp
    (Real.pow_div_factorial_le_exp (a/2*x^2) (by positivity) N)
  have hm := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ (2/a)^N*Real.exp (-a*x^2) by positivity)
  have he : Real.exp (a/2*x^2)*Real.exp (-a*x^2)=Real.exp (-(a/2)*x^2) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hl : (a/2*x^2)^N*((2/a)^N*Real.exp (-a*x^2))=
      x^(2*N)*Real.exp (-a*x^2) := by
    rw [mul_pow,div_pow,←pow_mul,div_pow]
    field_simp
  rw [hl] at hm
  calc _ ≤ (N.factorial:ℝ)*Real.exp (a/2*x^2)*((2/a)^N*Real.exp (-a*x^2)) := by simpa only [mul_comm (Real.exp (a/2*x^2)) (N.factorial:ℝ)] using hm
       _ = (N.factorial:ℝ)*(2/a)^N*(Real.exp (a/2*x^2)*Real.exp (-a*x^2)) := by ring
       _ = _ := by rw [he]
lemma gaussian_circle_moment_factorial (a : ℝ) (ha : 0 < a) (N : ℕ) :
    (∫x : ℝ in (-Real.pi)..Real.pi,x^(2*N)*Real.exp (-a*x^2)) ≤
      (N.factorial:ℝ)*(2/a)^N*Real.sqrt (2*Real.pi/a) := by
  have hp : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hf : Continuous (fun x : ℝ=>x^(2*N)*Real.exp (-a*x^2)) := by fun_prop
  have hg : Continuous (fun x : ℝ=>(N.factorial:ℝ)*(2/a)^N*Real.exp (-(a/2)*x^2)) := by fun_prop
  have hm := intervalIntegral.integral_mono_on hp (hf.intervalIntegrable (μ:=volume) _ _) (hg.intervalIntegrable (μ:=volume) _ _)
    (fun x hx=>gaussian_factorial_point_bound a x ha N)
  rw [intervalIntegral.integral_const_mul] at hm
  have hfull : (∫x : ℝ in (-Real.pi)..Real.pi,Real.exp (-(a/2)*x^2)) ≤
      Real.sqrt (Real.pi/(a/2)) := by
    rw [intervalIntegral.integral_of_le hp]
    have hb := setIntegral_le_integral (s:=Set.Ioc (-Real.pi) Real.pi)
      (integrable_exp_neg_mul_sq (half_pos ha)) (Filter.Eventually.of_forall (fun x=>(Real.exp_pos _).le))
    simpa only [integral_gaussian] using hb
  have hs : Real.pi/(a/2)=2*Real.pi/a := by ring
  rw [hs] at hfull
  exact hm.trans (mul_le_mul_of_nonneg_left hfull (by positivity))

end WP.Analysis
