import WPFormalization.Analysis.ParameterZeroValues
/-! Both endpoints of the actual boundary integral. The defining factorial
series proves I₀(z)=X′(−(z/2)²); the imaginary sine-kernel identity then gives
the hyperbolic-sine endpoint. The critical endpoint uses only T(y₀)=y₀ and
Delta(y₀)=0, without any assertion about r(y₀). No extra Bessel input is used. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma I₀_eq_derivX (z : ℂ) : I₀ z = deriv X (-(z/2)^2) := by
  have hs := Complex.hasSum_taylorSeries_of_entire X_differentiable.deriv 0 (-(z/2)^2)
  unfold I₀
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro n
  simp only [sub_zero,smul_eq_mul]
  rw [← iteratedDeriv_succ',iteratedDeriv_X_succ_zero]
  have hp : (-1:ℂ)^n*(-(z/2)^2)^n = (z/2)^(2*n) := by
    rw [← mul_pow,show (-1:ℂ)*(-(z/2)^2) = (z/2)^2 by ring,← pow_mul]
  rw [← hp]
  simp only [div_eq_mul_inv,inv_pow]
  ring
lemma sinh_kernel (x : ℝ) :
    x*(K 0 ((-x^2/2:ℝ):ℂ)).re = Real.sinh x := by
  have hs := rootKernel_sine ((x:ℂ)*Complex.I)
  have hz : ((x:ℂ)*Complex.I)^2/2 = ((-x^2/2:ℝ):ℂ) := by
    push_cast
    rw [mul_pow,Complex.I_sq]
    ring
  rw [hz,Complex.sin_mul_I,← Complex.ofReal_sinh] at hs
  have hi := congrArg Complex.im hs
  simpa only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,zero_add,add_zero,rootKernel,K] using hi
lemma boundary_zero_kernel (L : ℝ) :
    (∫ s : ℝ in (0)..1,(I₀ (L/Real.pi*Real.sqrt (WP.T 0-WP.Delta 0*s^2))).re) =
      (K 0 ((-L^2/8:ℝ):ℂ)).re := by
  have hD : WP.Delta 0 = Real.pi^2/4 := by simp only [WP.Delta,WP.T_zero_value,sub_zero]
  rw [WP.T_zero_value,hD]
  have hK := K_real_integral 0 (-L^2/8)
  simp only [Complex.ofReal_zero] at hK
  rw [hK]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc (0:ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using hs
  have hs2 : s^2 ≤ 1 := by nlinarith [hs'.1,hs'.2]
  have hnn : 0 ≤ Real.pi^2/4-Real.pi^2/4*s^2 := by
    have hm := mul_nonneg (by positivity : (0:ℝ) ≤ Real.pi^2/4) (sub_nonneg.mpr hs2)
    nlinarith
  have hS := Real.sq_sqrt hnn
  have heR : -(L/Real.pi*Real.sqrt (Real.pi^2/4-Real.pi^2/4*s^2)/2)^2 =
      0+(-L^2/8)/2*(1-s^2) := by
    calc
      _ = -(L^2*(Real.sqrt (Real.pi^2/4-Real.pi^2/4*s^2))^2)/(Real.pi^2*4) := by
        field_simp [Real.pi_ne_zero] <;> ring
      _ = -(L^2*(Real.pi^2/4-Real.pi^2/4*s^2))/(Real.pi^2*4) := by rw [hS]
      _ = _ := by field_simp [Real.pi_ne_zero] <;> ring
  have he := congrArg Complex.ofReal heR
  push_cast at he
  dsimp only
  rw [I₀_eq_derivX]
  unfold a
  push_cast
  rw [he]
lemma boundary_critical_constant (L : ℝ) :
    (∫ s : ℝ in (0)..1,(I₀ (L/Real.pi*Real.sqrt (WP.T y₀-WP.Delta y₀*s^2))).re) =
      (I₀ (Real.sqrt y₀*L/Real.pi)).re := by
  have hT : WP.T y₀ = y₀ := by simp only [WP.T,ite_true]
  have hD : WP.Delta y₀ = 0 := by simp only [WP.Delta,hT,sub_self]
  rw [hT,hD]
  simp only [zero_mul,sub_zero,intervalIntegral.integral_const,sub_zero,one_smul]
  congr 1
  congr 1
  push_cast
  ring
lemma boundary_endpoints_integral (L : ℝ) :
    (∫ s : ℝ in (0)..1,(I₀ (L/Real.pi*Real.sqrt (WP.T 0-WP.Delta 0*s^2))).re) =
      (if L = 0 then 1 else Real.sinh (L/2)/(L/2)) ∧
    (∫ s : ℝ in (0)..1,(I₀ (L/Real.pi*Real.sqrt (WP.T y₀-WP.Delta y₀*s^2))).re) =
      (I₀ (Real.sqrt y₀*L/Real.pi)).re := by
  refine ⟨?_,boundary_critical_constant L⟩
  rw [boundary_zero_kernel]
  by_cases hL : L = 0
  · simp only [hL,zero_pow (by norm_num : 2 ≠ 0),neg_zero,zero_div,Complex.ofReal_zero,K_zero,
      derivX_zero,Complex.one_re,ite_true]
  · rw [if_neg hL]
    have hx : L/2 ≠ 0 := div_ne_zero hL (by norm_num)
    have hs := sinh_kernel (L/2)
    have he : (-(L/2)^2/2:ℝ) = -L^2/8 := by ring
    rw [he] at hs
    apply (eq_div_iff hx).mpr
    simpa only [mul_comm] using hs
end WP.Analysis
