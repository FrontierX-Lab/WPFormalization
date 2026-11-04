import WPFormalization.Statements.Basic

/-! Differentiation under the fixed interval integral and integration by parts for the
analytic kernels. All lemmas are proved from Mathlib; no paper-specific estimates are assumed. -/
noncomputable section
namespace WP
open MeasureTheory Filter Set Metric
open scoped Topology

lemma hasDerivAt_kernelIntegral (q : ℝ → ℂ) (hq : Continuous q) (g : ℂ → ℂ) (hg : Differentiable ℂ g) (Y z : ℂ) :
    HasDerivAt (fun w : ℂ => ∫ s : ℝ in (0)..1, q s*g (Y+w/2*(1-(s : ℂ)^2)))
      (∫ s : ℝ in (0)..1, q s*(1-(s : ℂ)^2)/2*deriv g (Y+z/2*(1-(s : ℂ)^2))) z := by
  let F (w : ℂ) (s : ℝ) : ℂ := q s*g (Y+w/2*(1-(s : ℂ)^2))
  let F' (w : ℂ) (s : ℝ) : ℂ :=
    q s*(1-(s : ℂ)^2)/2*deriv g (Y+w/2*(1-(s : ℂ)^2))
  have hc : Continuous g := hg.continuous
  have hc' : Continuous (deriv g) := continuous_iff_continuousAt.mpr
    (fun w => ((hg.analyticAt w).deriv).continuousAt)
  have hF (w : ℂ) : Continuous (F w) := by dsimp [F]; fun_prop
  have hF' : Continuous (fun p : ℂ × ℝ => F' p.1 p.2) := by dsimp [F']; fun_prop
  obtain ⟨C,hC⟩ := ((isCompact_closedBall z 1).prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).bddAbove_image hF'.norm.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => C) (ball_mem_nhds z zero_lt_one)
    ?_ ((hF z).intervalIntegrable 0 1) ?_ ?_ (intervalIntegrable_const) ?_).2
  · filter_upwards with w
    exact (hF w).aestronglyMeasurable
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards with s hs w hw
    apply hC
    refine ⟨(w,s), ⟨mem_closedBall.mpr (le_of_lt (mem_ball.mp hw)), ?_⟩, rfl⟩
    simpa using Ioc_subset_Icc_self hs
  · filter_upwards with s hs w hw
    dsimp [F,F']
    convert ((hg _).hasDerivAt.comp w
      ((((hasDerivAt_id w).div_const 2).mul_const (1-(s : ℂ)^2)).const_add Y)).const_mul (q s) using 1 <;> dsimp only [Function.comp_def, id_eq] <;> ring

lemma kernelPath_hasDerivAt (g : ℂ → ℂ) (hg : Differentiable ℂ g) (Y z : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => g (Y+z/2*(1-(t : ℂ)^2)))
      (-z*s*deriv g (Y+z/2*(1-(s : ℂ)^2))) s := by
  have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
  have hpoly := (((hcast.pow 2).const_sub 1).const_mul (z/2)).const_add Y
  convert (hg _).hasDerivAt.comp s hpoly using 1 <;>
    dsimp only [Function.comp_def,Pi.pow_apply,Pi.mul_apply] <;> ring

lemma kernelIntegral_relation (g : ℂ → ℂ) (hg : Differentiable ℂ g) (Y z : ℂ) :
    (∫ s : ℝ in (0)..1, g (Y+z/2*(1-(s : ℂ)^2))) =
      3*(∫ s : ℝ in (0)..1, (s : ℂ)^2*g (Y+z/2*(1-(s : ℂ)^2))) +
      2*z*(∫ s : ℝ in (0)..1, (s : ℂ)^2*(1-(s : ℂ)^2)/2*deriv g (Y+z/2*(1-(s : ℂ)^2))) := by
  let F (s : ℝ) : ℂ := g (Y+z/2*(1-(s : ℂ)^2))
  let Q (s : ℝ) : ℂ := (s : ℂ)^2*F s
  let R (s : ℝ) : ℂ := (s : ℂ)^2*(1-(s : ℂ)^2)/2*deriv g (Y+z/2*(1-(s : ℂ)^2))
  have hc : Continuous g := hg.continuous
  have hc' : Continuous (deriv g) := continuous_iff_continuousAt.mpr
    (fun w => ((hg.analyticAt w).deriv).continuousAt)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hQ : Continuous Q := by dsimp [Q]; fun_prop
  have hR : Continuous R := by dsimp [R]; fun_prop
  have hp (s : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ)*(1-(t : ℂ)^2)*F t)
      (F s-3*Q s-2*z*R s) s := by
    have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
    have hpoly := hcast.mul ((hcast.pow 2).const_sub 1)
    convert hpoly.mul (kernelPath_hasDerivAt g hg Y z s) using 1 <;>
      dsimp only [F,Q,R,Pi.mul_apply,Pi.pow_apply] <;> ring
  have hFi : IntervalIntegrable F volume 0 1 := hF.intervalIntegrable 0 1
  have hQi : IntervalIntegrable (fun s => 3*Q s) volume 0 1 := (continuous_const.mul hQ).intervalIntegrable 0 1
  have hRi : IntervalIntegrable (fun s => 2*z*R s) volume 0 1 := (continuous_const.mul hR).intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun s _ => hp s) ((hFi.sub hQi).sub hRi)
  simp only [Complex.ofReal_one, one_pow, sub_self, mul_zero, zero_mul,
    Complex.ofReal_zero, mul_zero, sub_self] at hFTC
  rw [intervalIntegral.integral_sub (hFi.sub hQi) hRi,
    intervalIntegral.integral_sub hFi hQi,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
  change (∫ s in (0)..1, F s) = 3*(∫ s in (0)..1, Q s)+2*z*(∫ s in (0)..1, R s)
  linear_combination hFTC

/- All complex derivatives of the integral are obtained by multiplying the fixed weight. -/
lemma iteratedDeriv_differentiable_of_entire (g : ℂ → ℂ) (hg : Differentiable ℂ g) (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n g) := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact fun z => ((ih.analyticAt z).deriv).differentiableAt
lemma iteratedDeriv_kernelIntegral (q : ℝ → ℂ) (hq : Continuous q)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (n : ℕ) (Y z : ℂ) :
    iteratedDeriv n (fun w : ℂ => ∫ s : ℝ in (0)..1, q s*g (Y+w/2*(1-(s : ℂ)^2))) z =
      ∫ s : ℝ in (0)..1, q s*((1-(s : ℂ)^2)/2)^n *
        iteratedDeriv n g (Y+z/2*(1-(s : ℂ)^2)) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun w : ℂ => ∫ s : ℝ in (0)..1, q s*g (Y+w/2*(1-(s : ℂ)^2))) =
      fun w : ℂ => ∫ s : ℝ in (0)..1, q s*((1-(s : ℂ)^2)/2)^n *
        iteratedDeriv n g (Y+w/2*(1-(s : ℂ)^2)) := funext ih
    rw [heq]
    rw [(hasDerivAt_kernelIntegral (fun s => q s*((1-(s : ℂ)^2)/2)^n)
      (by fun_prop) (iteratedDeriv n g) (iteratedDeriv_differentiable_of_entire g hg n) Y z).deriv]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [iteratedDeriv_succ, pow_succ]
    ring

/- Exact polynomial beta moments used for the Taylor coefficients in Eq.2.1. -/
def kernelMoment (n : ℕ) : ℂ := ∫ s : ℝ in (0)..1, ((1-(s : ℂ)^2)/2)^n
def kernelSecondMoment (n : ℕ) : ℂ := ∫ s : ℝ in (0)..1, (s : ℂ)^2*((1-(s : ℂ)^2)/2)^n
lemma oddFactorial_succ (n : ℕ) : oddFactorial (n+1) = oddFactorial n*(2*n+3) := by
  unfold oddFactorial
  rw [Finset.prod_range_succ]
  congr 1
lemma oddFactorial_ne_zero (n : ℕ) : oddFactorial n ≠ 0 := by
  unfold oddFactorial
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  omega
lemma kernelMoment_relation (n : ℕ) : kernelMoment (n+1) = (n+1 : ℂ)*kernelSecondMoment n ∧
    kernelMoment n = (2*n+3 : ℂ)*kernelSecondMoment n := by
  let q (s : ℝ) : ℂ := (1-(s : ℂ)^2)/2
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ)*q t^(n+1))
      (q s^(n+1)-(n+1 : ℂ)*(s : ℂ)^2*q s^n) s := by
    have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
    have hqderiv := ((hcast.pow 2).const_sub 1).div_const 2
    convert hcast.mul (hqderiv.pow (n+1)) using 1 <;>
      dsimp only [q, Pi.pow_apply, Pi.mul_apply] <;>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] <;> ring
  have hqi : IntervalIntegrable (fun s => q s^(n+1)) volume 0 1 :=
    (hq.pow _).intervalIntegrable 0 1
  have hsi : IntervalIntegrable (fun s => (n+1 : ℂ)*(s : ℂ)^2*q s^n) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun s _ => hd s) (hqi.sub hsi)
  simp only [q, Complex.ofReal_zero, Complex.ofReal_one, one_pow, zero_pow (by omega : n+1 ≠ 0),
    sub_self, zero_mul, mul_zero, zero_div, sub_self] at h
  rw [intervalIntegral.integral_sub hqi hsi] at h
  have hmul : (∫ x : ℝ in (0)..1, (n+1 : ℂ)*(x : ℂ)^2*q x^n) =
      (n+1 : ℂ)*∫ x : ℝ in (0)..1, (x : ℂ)^2*q x^n := by
    simpa only [mul_assoc] using
      intervalIntegral.integral_const_mul (n+1 : ℂ) (fun x : ℝ => (x : ℂ)^2*q x^n)
  rw [hmul] at h
  have hrec : kernelMoment (n+1) = (n+1 : ℂ)*kernelSecondMoment n := by
    change kernelMoment (n+1)-(n+1 : ℂ)*kernelSecondMoment n = 0 at h
    linear_combination h
  have heq (s : ℝ) : q s^n = 2*q s^(n+1)+(s : ℂ)^2*q s^n := by
    rw [pow_succ]
    dsimp [q]
    ring
  have hc : kernelMoment n = 2*kernelMoment (n+1)+kernelSecondMoment n := by
    unfold kernelMoment kernelSecondMoment
    change (∫ s in (0)..1, q s^n) = 2*(∫ s in (0)..1, q s^(n+1))+
      (∫ s in (0)..1, (s : ℂ)^2*q s^n)
    calc
      _ = ∫ s in (0)..1, 2*q s^(n+1)+(s : ℂ)^2*q s^n :=
        intervalIntegral.integral_congr (fun s hs => heq s)
      _ = _ := by
        rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
        · exact (continuous_const.mul (hq.pow _)).intervalIntegrable 0 1
        · exact (by fun_prop : Continuous (fun s : ℝ => (s : ℂ)^2*q s^n)).intervalIntegrable 0 1
  constructor
  · exact hrec
  · rw [hrec] at hc
    linear_combination hc
lemma kernelMoment_eval (n : ℕ) : kernelMoment n = (n.factorial : ℂ)/oddFactorial n := by
  induction n with
  | zero => norm_num [kernelMoment,oddFactorial]
  | succ n ih =>
    obtain ⟨h1,h2⟩ := kernelMoment_relation n
    rw [ih] at h2
    rw [Nat.factorial_succ, oddFactorial_succ, Nat.cast_mul]
    have hf : (oddFactorial n : ℂ) ≠ 0 := by exact_mod_cast oddFactorial_ne_zero n
    have hn : (2*n+3 : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2*n+3 ≠ 0)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at *
    field_simp [hf,hn] at h2 ⊢
    linear_combination (oddFactorial n : ℂ)*(2*n+3 : ℂ)*h1-(n+1 : ℂ)*h2
lemma kernelSecondMoment_eval (n : ℕ) : kernelSecondMoment n = (n.factorial : ℂ)/oddFactorial (n+1) := by
  have hr := (kernelMoment_relation n).2
  rw [kernelMoment_eval] at hr
  rw [oddFactorial_succ, Nat.cast_mul]
  have hf : (oddFactorial n : ℂ) ≠ 0 := by exact_mod_cast oddFactorial_ne_zero n
  have hn : (2*n+3 : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2*n+3 ≠ 0)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at *
  field_simp [hf,hn] at hr ⊢
  linear_combination -hr
end WP
