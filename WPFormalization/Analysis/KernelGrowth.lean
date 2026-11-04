import WPFormalization.Analysis.CharacteristicBounds

/-! The actual derivative and integral kernels have growth of order at most
one half. The factorial-square series is bounded by the square of the real
exponential series; the integral bound then gives the required entire-kernel
growth estimate. No zero classification or product theorem is assumed. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma derivX_hasSum_complex (z : ℂ) :
    HasSum (fun n : ℕ => (-1:ℂ)^n*z^n/(n.factorial:ℂ)^2) (deriv X z) := by
  have hf : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  convert Complex.hasSum_taylorSeries_of_entire hf 0 z using 1
  ext n
  rw [← iteratedDeriv_succ',iteratedDeriv_X_succ_zero]
  simp only [sub_zero,smul_eq_mul]
  ring
lemma derivX_norm_growth (z : ℂ) : ‖deriv X z‖ ≤ Real.exp (2*Real.sqrt ‖z‖) := by
  let x := Real.sqrt ‖z‖
  let c : ℕ → ℝ := fun n => x^n/(n.factorial:ℝ)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hc (n : ℕ) : 0 ≤ c n := by dsimp [c]; positivity
  have hs : HasSum c (Real.exp x) := by
    simpa only [c,← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x
  have hcle (n : ℕ) : c n ≤ Real.exp x := hs.summable.le_tsum n (fun i _=>hc i) |>.trans_eq hs.tsum_eq
  have hnorm (n : ℕ) : ‖(-1:ℂ)^n*z^n/(n.factorial:ℂ)^2‖ = c n^2 := by
    rw [norm_div,norm_mul,norm_pow,norm_pow,norm_pow]
    simp only [norm_neg,norm_one,one_pow,one_mul,Complex.norm_natCast]
    dsimp [c]
    rw [div_pow,← pow_mul,pow_mul',Real.sq_sqrt (norm_nonneg z)]
  have he : Real.exp x*Real.exp x = Real.exp (2*x) := by rw [← Real.exp_add];ring_nf
  rw [← he]
  apply (derivX_hasSum_complex z).norm_le_of_bounded (hs.mul_left (Real.exp x))
  intro n
  rw [hnorm,pow_two]
  exact mul_le_mul_of_nonneg_right (hcle n) (hc n)
lemma K_norm_growth_point (Y : ℝ) (hY : 0≤Y) (z : ℂ) :
    ‖K Y z‖ ≤ Real.exp (2*Real.sqrt (Y+‖z‖)) := by
  have hb (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖deriv X ((Y:ℂ)+z/2*(1-(s:ℂ)^2))‖ ≤ Real.exp (2*Real.sqrt (Y+‖z‖)) := by
    have hc : 0≤(1-s^2)/2 ∧ (1-s^2)/2≤1 := by
      constructor <;> nlinarith [hs.1,hs.2,sq_nonneg s]
    have he : z/2*(1-(s:ℂ)^2) = z*(((1-s^2)/2:ℝ):ℂ) := by push_cast;ring
    have ha : ‖(Y:ℂ)+z/2*(1-(s:ℂ)^2)‖ ≤ Y+‖z‖ := by
      calc
        _ ≤ ‖(Y:ℂ)‖+‖z/2*(1-(s:ℂ)^2)‖ := norm_add_le _ _
        _ = Y+‖z‖*((1-s^2)/2) := by
          rw [he,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
            Real.norm_eq_abs,abs_of_nonneg hY,abs_of_nonneg hc.1]
        _ ≤ Y+‖z‖ := by nlinarith [norm_nonneg z]
    exact (derivX_norm_growth _).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ha) (by norm_num)))
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (f:=fun s : ℝ => deriv X ((Y:ℂ)+z/2*(1-(s:ℂ)^2)))
    (fun s hs => by
      have hs' : s ∈ Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
      exact hb s ⟨hs'.1.le,hs'.2⟩)
  simpa only [K,sub_zero,abs_one,mul_one] using hh
lemma K_norm_growth (Y : ℝ) (hY : 0≤Y) (z : ℂ) :
    ‖K Y z‖ ≤ Real.exp (2*Real.sqrt Y)*Real.exp (2*Real.sqrt ‖z‖) := by
  have hs : Real.sqrt (Y+‖z‖) ≤ Real.sqrt Y+Real.sqrt ‖z‖ := by
    apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
    nlinarith [Real.sq_sqrt hY,Real.sq_sqrt (norm_nonneg z),
      mul_nonneg (Real.sqrt_nonneg Y) (Real.sqrt_nonneg ‖z‖)]
  calc
    _ ≤ Real.exp (2*Real.sqrt (Y+‖z‖)) := K_norm_growth_point Y hY z
    _ ≤ Real.exp (2*Real.sqrt Y+2*Real.sqrt ‖z‖) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_add _ _
end WP.Analysis
