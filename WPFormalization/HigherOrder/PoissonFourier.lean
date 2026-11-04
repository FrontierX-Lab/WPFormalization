import WPFormalization.HigherOrder.PoissonCoefficientOperator
import WPFormalization.Analysis.HarmonicFourierScaling
/-! Exact circle coefficient representation and Gaussian bound for the actual Poisson operator. -/
noncomputable section
namespace WP.HigherOrder
open MeasureTheory
open scoped Topology
lemma poissonCoefficientOperator_fourier (h ρ : ℝ) (hh : 0 < h) (_hρ : 0 < ρ)
    (k : ℕ) (hk : 1 ≤ k) (hν : (k:ℝ)/h < ρ)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.ball 0 ρ)) :
    poissonCoefficientOperator h k f=
      ((k.factorial:ℂ)*Complex.exp (k:ℂ)/(k:ℂ)^k)*((2*Real.pi:ℝ):ℂ)⁻¹*
        ∫θ:ℝ in (-Real.pi)..Real.pi,
          Complex.exp ((k:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1-(θ:ℂ)*Complex.I))*
            f ((((k:ℝ)/h:ℝ):ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) := by
  let ν : ℝ := (k:ℝ)/h
  let F : ℂ → ℂ := fun u=>Complex.exp ((h:ℂ)*u)*f u
  let g : ℂ → ℂ := fun w=>F ((ν:ℂ)*w)
  have hνp : 0 < ν := div_pos (by exact_mod_cast hk) hh
  have hkp : (k:ℂ)≠0 := by exact_mod_cast (show k≠0 by omega)
  have hhc : (h:ℂ)≠0 := by exact_mod_cast hh.ne'
  have hcν : (h:ℂ)*(ν:ℂ)=(k:ℂ) := by dsimp [ν];push_cast;field_simp
  have hg : DifferentiableOn ℂ g (Metric.closedBall 0 1) := by
    intro w hw
    have hw' : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
    have hwρ : ‖(ν:ℂ)*w‖ < ρ := by
      rw [norm_mul,Complex.norm_of_nonneg hνp.le]
      exact (mul_le_of_le_one_right hνp.le hw').trans_lt hν
    have ha : DifferentiableAt ℂ f ((ν:ℂ)*w) :=
      (hf _ (by simpa only [Metric.mem_ball,dist_zero_right] using hwρ)).differentiableAt
    exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ=>Complex.exp ((h:ℂ)*((ν:ℂ)*w))) w).mul
      (ha.comp w (by fun_prop))).differentiableWithinAt
  have hc : WP.coeff g k=(ν:ℂ)^k*WP.coeff F k := by
    rw [WP.coeff,Analysis.iteratedDeriv_comp_mul_left,mul_zero,mul_div_assoc]
    rfl
  have hi := Analysis.coeff_eq_symmetric_fourier_integral g hg k
  have heθ (θ : ℝ) : Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*g (Complex.exp ((θ:ℂ)*Complex.I))=
      Complex.exp (k:ℂ)*(Complex.exp ((k:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1-(θ:ℂ)*Complex.I))*
        f ((ν:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) := by
    dsimp only [g,F]
    rw [←mul_assoc,←Complex.exp_add]
    have hex : -(k:ℂ)*(θ:ℂ)*Complex.I+(h:ℂ)*((ν:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))=
        (k:ℂ)+(k:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1-(θ:ℂ)*Complex.I) := by
      rw [←mul_assoc,hcν]
      ring
    rw [hex,Complex.exp_add]
    ring
  have hefun : (fun θ : ℝ=>Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*g (Complex.exp ((θ:ℂ)*Complex.I)))=
      (fun θ : ℝ=>Complex.exp (k:ℂ)*(Complex.exp ((k:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1-(θ:ℂ)*Complex.I))*
        f ((ν:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)))) := funext heθ
  rw [hefun,intervalIntegral.integral_const_mul] at hi
  calc poissonCoefficientOperator h k f=(k.factorial:ℂ)/(k:ℂ)^k*WP.coeff g k := by
        rw [hc,poissonCoefficientOperator]
        dsimp [ν,F]
        push_cast
        rw [div_pow]
        field_simp
       _ = _ := by rw [hi];dsimp only [ν];ring

lemma poisson_fourier_kernel_norm (k : ℕ) (θ : ℝ) :
    ‖Complex.exp ((k:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1-(θ:ℂ)*Complex.I))‖=
      Real.exp ((k:ℝ)*(Real.cos θ-1)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re,Complex.exp_mul_I,←Complex.ofReal_cos]

lemma poisson_fourier_kernel_gaussian (k : ℕ) (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    ‖Complex.exp ((k:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1-(θ:ℂ)*Complex.I))‖ ≤
      Real.exp (-(2/Real.pi^2)*(k:ℝ)*θ^2) := by
  rw [poisson_fourier_kernel_norm]
  apply Real.exp_le_exp.mpr
  have ht := mul_le_mul_of_nonneg_left (Real.cos_le_one_sub_mul_cos_sq hθ) (Nat.cast_nonneg k)
  nlinarith

end WP.HigherOrder
