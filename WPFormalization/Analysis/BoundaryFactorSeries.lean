import WPFormalization.Analysis.BoundaryBetaMoment
import WPFormalization.Marked.ExternalStringBoundary
import WPFormalization.Analysis.BoundaryFactorBasic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Exact one-boundary factorization. Taylor expansion of the genuine entire
translation kernel at tY and dominated integration produce the original I₀
boundary integral. The beta moments supply the exact odd-factorial weights. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory WP.BoundaryConvolution
open scoped Topology

lemma boundary_translation_iteratedDeriv (b n : ℕ) :
    iteratedDeriv n (translationKernel b) = translationKernel (b+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext z
    rw [(translationKernel_hasDerivAt (b+n) z).deriv]
    congr 1

lemma boundary_kernel_translation_hasSum (u v : ℝ) :
    HasSum (fun b : ℕ => v^b/(b.factorial:ℝ)*(translationKernel b (u:ℂ)).re)
      ((translationKernel 0 ((u+v:ℝ):ℂ)).re) := by
  have hf : Differentiable ℂ (translationKernel 0) :=
    fun z => (translationKernel_analyticAt 0 z).differentiableAt
  have hs := (Complex.hasSum_taylorSeries_of_entire hf (u:ℂ) ((u+v:ℝ):ℂ)).mapL Complex.reCLM
  convert hs using 1
  · ext b
    rw [boundary_translation_iteratedDeriv]
    simp only [zero_add,smul_eq_mul,Complex.reCLM_apply]
    have hz : ((u+v:ℝ):ℂ)-(u:ℂ)=(v:ℂ) := by push_cast;ring
    rw [hz,translationKernel_ofReal]
    simp only [←Complex.ofReal_natCast,←Complex.ofReal_inv,←Complex.ofReal_pow,←Complex.ofReal_div,
      ←Complex.ofReal_mul,Complex.ofReal_re]
    ring
  · rfl

lemma boundary_I₀_translation (L U : ℝ) (hU : 0 ≤ U) :
    (I₀ ((L/Real.pi*Real.sqrt U:ℝ):ℂ)).re =
      (translationKernel 0 (((L^2/(4*Real.pi^2))*U:ℝ):ℂ)).re := by
  rw [I₀_eq_derivX]
  simp only [translationKernel,pow_zero,one_mul,Nat.zero_add,iteratedDeriv_one]
  congr 2
  push_cast
  have he := Real.sq_sqrt hU
  have hz : -((L/Real.pi*Real.sqrt U:ℝ)/2)^2 = -(L^2/(4*Real.pi^2)*U) := by
    field_simp
    nlinarith [he]
  have hzc := congrArg Complex.ofReal hz
  push_cast at hzc
  exact hzc

lemma boundary_translation_integral_hasSum (u d : ℝ) (hu : 0 ≤ u) (hd : 0 ≤ d) :
    HasSum (fun b : ℕ => d^b/(b.factorial:ℝ)*(translationKernel b (u:ℂ)).re*
        boundaryBetaMoment b)
      (∫ s : ℝ in (0)..1,(translationKernel 0 ((u+d*(1-s^2):ℝ):ℂ)).re) := by
  let F (b : ℕ) (s : ℝ) : ℝ :=
    d^b/(b.factorial:ℝ)*(translationKernel b (u:ℂ)).re*(1-s^2)^b
  let B (b : ℕ) : ℝ := d^b/(b.factorial:ℝ)*(translationKernel b (u:ℂ)).re
  have hB : Summable B := (boundary_kernel_translation_hasSum u d).summable
  have hF (b : ℕ) : Continuous (F b) := by dsimp [F];fun_prop
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ:=volume) (a:= (0:ℝ)) (b:=1)
    (F:=F) (f:=fun s:ℝ=>(translationKernel 0 ((u+d*(1-s^2):ℝ):ℂ)).re)
    (fun b _ => B b) (fun b => (hF b).aestronglyMeasurable) ?_ ?_
    (intervalIntegrable_const) ?_
  · convert hi using 1
    ext b
    dsimp only [F,B,boundaryBetaMoment]
    rw [intervalIntegral.integral_const_mul]
  · intro b
    apply ae_of_all
    intro s hs
    have hs0 : s ∈ Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs0.1.le,hs0.2⟩
    have hs2 : s^2 ≤ 1 := pow_le_one₀ hs'.1 hs'.2
    have hq : 0 ≤ 1-s^2 ∧ 1-s^2 ≤ 1 := by constructor <;> nlinarith [sq_nonneg s]
    have hweight : 0 ≤ B b := by dsimp [B];exact mul_nonneg (by positivity) (translationKernel_nonneg b u hu)
    change |B b*(1-s^2)^b| ≤ B b
    rw [abs_of_nonneg (mul_nonneg hweight (pow_nonneg hq.1 _))]
    exact mul_le_of_le_one_right hweight (pow_le_one₀ hq.1 hq.2)
  · exact ae_of_all _ (fun _ _ => hB)
  · apply ae_of_all
    intro s _
    convert boundary_kernel_translation_hasSum u (d*(1-s^2)) using 1
    ext b
    dsimp only [F]
    rw [mul_pow]
    ring

/-- The original I₀ boundary integral is the convergent one-boundary series
in the genuine translation kernel. The stationary first root is used only
on its physical half-open domain. -/
lemma boundaryFactor_translation_hasSum (Y L : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) :
    HasSum (fun b : ℕ => r Y^b/(oddFactorial b:ℝ)*(L^2/(4*Real.pi^2))^b*
      (translationKernel b (((L^2/(4*Real.pi^2))*Y:ℝ):ℂ)).re)
      (boundaryFactor Y L) := by
  let t := L^2/(4*Real.pi^2)
  have ht : 0 ≤ t := by dsimp [t];positivity
  have hD := Delta_pos Y hY
  have hs := boundary_translation_integral_hasSum (t*Y) (t*Delta Y)
    (mul_nonneg ht hY.1) (mul_nonneg ht hD.le)
  have hr : 2*Delta Y=r Y := by
    have he := T_eq_firstKernelEndpoint Y hY
    unfold Delta
    linarith
  have hinter : (∫ s : ℝ in (0)..1,
      (translationKernel 0 ((t*Y+(t*Delta Y)*(1-s^2):ℝ):ℂ)).re) = boundaryFactor Y L := by
    unfold boundaryFactor
    apply intervalIntegral.integral_congr
    intro s hs
    have hsq : s^2 ≤ 1 := by
      have hs' : s ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
      exact pow_le_one₀ hs'.1 hs'.2
    have hU : 0 ≤ T Y-Delta Y*s^2 := by
      have hp := mul_nonneg hD.le (sub_nonneg.mpr hsq)
      unfold Delta at *
      linarith [hY.1]
    have he := boundary_I₀_translation L (T Y-Delta Y*s^2) hU
    have heq : t*Y+(t*Delta Y)*(1-s^2)=t*(T Y-Delta Y*s^2) := by
      unfold Delta
      ring
    dsimp only
    rw [heq]
    simpa only [t,Complex.ofReal_mul,Complex.ofReal_div] using he.symm
  rw [hinter] at hs
  convert hs using 1
  ext b
  rw [boundaryBetaMoment_value]
  have hfact : (b.factorial:ℝ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have hodd : (oddFactorial b:ℝ) ≠ 0 := by exact_mod_cast oddFactorial_ne_zero b
  have hscale : 2*(t*Delta Y)=r Y*t := by rw [mul_left_comm 2 t,hr];ring
  change r Y^b/(oddFactorial b:ℝ)*t^b*(translationKernel b ((t*Y:ℝ):ℂ)).re = _
  calc
    _ = (2*(t*Delta Y))^b/(oddFactorial b:ℝ)*
        (translationKernel b ((t*Y:ℝ):ℂ)).re := by rw [hscale,mul_pow];ring
    _ = _ := by
      rw [mul_pow]
      field_simp [hfact,hodd]
      <;> ring

lemma boundaryFactor_realTranslationWeight_hasSum (Y L : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) :
    HasSum (fun b : ℕ => r Y^b/(oddFactorial b:ℝ)*
      realTranslationWeight (L^2/(4*Real.pi^2)) b Y) (boundaryFactor Y L) := by
  convert boundaryFactor_translation_hasSum Y L hY using 1
  ext b
  simp only [realTranslationWeight,translationWeight,←Complex.ofReal_pow,←Complex.ofReal_mul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

end WP.Analysis
