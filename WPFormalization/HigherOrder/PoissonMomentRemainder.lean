import WPFormalization.HigherOrder.PoissonFourier
import WPFormalization.Analysis.PoissonPeakBounds
import WPFormalization.Analysis.GaussianFactorialMoments
noncomputable section
namespace WP.HigherOrder
open MeasureTheory
open scoped Topology
lemma poissonCoefficientOperator_circle_moment_bound (h ρ M : ℝ) (hh : 0 < h) (hρ : 0 < ρ)
    (hM : 0 ≤ M) (k N : ℕ) (hk : 1 ≤ k) (hν : (k:ℝ)/h < ρ)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.ball 0 ρ))
    (hb : ∀θ∈Set.Icc (-Real.pi) Real.pi,
      ‖f ((((k:ℝ)/h:ℝ):ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖ ≤ M*θ^(2*N)) :
    ‖poissonCoefficientOperator h k f‖ ≤
      Analysis.poissonPeakInverse k/(2*Real.pi)*M*(N.factorial:ℝ)*
        (Real.pi^2/(k:ℝ))^N*Real.sqrt (Real.pi^3/(k:ℝ)) := by
  let G : ℝ → ℂ := fun θ=>
    Complex.exp ((k:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1-(θ:ℂ)*Complex.I))*
      f ((((k:ℝ)/h:ℝ):ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
  let a : ℝ := 2/Real.pi^2*(k:ℝ)
  have hkp : 0 < (k:ℝ) := by exact_mod_cast hk
  have ha : 0 < a := by dsimp [a];positivity
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hgcont : Continuous G := by
    apply Continuous.mul (by fun_prop)
    apply continuousOn_univ.mp
    apply hf.continuousOn.comp (by fun_prop : ContinuousOn (fun θ : ℝ=>(((k:ℝ)/h:ℝ):ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) Set.univ)
    intro θ hθ
    rw [Metric.mem_ball,dist_zero_right,norm_mul,Complex.norm_of_nonneg (by positivity)]
    have he : ‖Complex.exp ((θ:ℂ)*Complex.I)‖=1 := by simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I θ
    rw [he,mul_one]
    exact hν
  have hb' (θ : ℝ) (hθ : θ∈Set.Icc (-Real.pi) Real.pi) :
      ‖G θ‖ ≤ M*(θ^(2*N)*Real.exp (-a*θ^2)) := by
    have hθπ : |θ| ≤ Real.pi := abs_le.mpr hθ
    have he := poisson_fourier_kernel_gaussian k θ hθπ
    have he' : ‖Complex.exp ((k:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1-(θ:ℂ)*Complex.I))‖ ≤ Real.exp (-a*θ^2) := by simpa only [a,neg_mul] using he
    dsimp only [G]
    rw [norm_mul]
    calc _ ≤ Real.exp (-a*θ^2)*(M*θ^(2*N)) :=
          mul_le_mul he' (hb θ hθ) (norm_nonneg _) (Real.exp_pos _).le
         _ = _ := by ring
  have hc : ‖(k.factorial:ℂ)*Complex.exp (k:ℂ)/(k:ℂ)^k‖=Analysis.poissonPeakInverse k := by
    simp [Analysis.poissonPeakInverse,norm_pow,Complex.norm_exp]
  rw [poissonCoefficientOperator_fourier h ρ hh hρ k hk hν f hf,norm_mul,norm_mul,hc,norm_inv,
    Complex.norm_of_nonneg (by positivity : (0:ℝ)≤2*Real.pi)]
  have htriangle := intervalIntegral.norm_integral_le_integral_norm (μ:=volume) hπ (f:=G)
  have hmajor : Continuous (fun θ : ℝ=>M*(θ^(2*N)*Real.exp (-a*θ^2))) := by fun_prop
  have hint := intervalIntegral.integral_mono_on hπ
    (hgcont.norm.intervalIntegrable (μ:=volume) _ _)
    (hmajor.intervalIntegrable (μ:=volume) _ _)
    hb'
  rw [intervalIntegral.integral_const_mul] at hint
  have hm := Analysis.gaussian_circle_moment_factorial a ha N
  have hraw := htriangle.trans (hint.trans (mul_le_mul_of_nonneg_left hm hM))
  have h2a : 2/a=Real.pi^2/(k:ℝ) := by dsimp [a];field_simp
  have hpa : 2*Real.pi/a=Real.pi^3/(k:ℝ) := by dsimp [a];field_simp
  rw [h2a,hpa] at hraw
  have ht := mul_le_mul_of_nonneg_left hraw
    (show 0 ≤ Analysis.poissonPeakInverse k*(2*Real.pi)⁻¹ by positivity [Analysis.poissonPeakInverse_pos k])
  simpa only [G,div_eq_mul_inv,mul_assoc] using ht
end WP.HigherOrder
