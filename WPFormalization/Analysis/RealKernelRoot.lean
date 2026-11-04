import WPFormalization.Analysis.AffineIntegral
import WPFormalization.Analysis.PositiveRootInfimum

/-! Existence of a positive real zero of the integral kernel. This file is
upstream of Statements.Kernels: it works with the displayed integral itself.
The argument follows a characteristic along which its weighted derivative
is negative, starting at an exact sine zero. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
set_option maxHeartbeats 600000

def rootKernel (Y z : ℂ) : ℂ :=
  ∫ s : ℝ in (0)..1, deriv X (Y+z/2*(1-(s : ℂ)^2))

lemma rootKernel_differentiable (Y : ℂ) : Differentiable ℂ (rootKernel Y) := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  intro z
  change DifferentiableAt ℂ
    (fun w => ∫ s : ℝ in (0)..1, deriv X (Y+w/2*(1-(s:ℂ)^2))) z
  simpa only [one_mul] using
    (hasDerivAt_kernelIntegral (fun _ => 1) continuous_const (deriv X) hg Y z).differentiableAt

lemma rootKernel_zero (Y : ℂ) : rootKernel Y 0 = deriv X Y := by simp [rootKernel]

lemma rootKernel_jets_zero (n : ℕ) :
    iteratedDeriv n (rootKernel 0) 0 = (-1 : ℂ)^n / oddFactorial n := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  have h := iteratedDeriv_kernelIntegral (fun _ => 1) continuous_const (deriv X) hg n 0 0
  simp only [zero_div,zero_mul,add_zero,one_mul,← iteratedDeriv_succ'] at h
  change iteratedDeriv n (rootKernel 0) 0 = _ at h
  rw [h,intervalIntegral.integral_mul_const]
  change kernelMoment n * _ = _
  rw [kernelMoment_eval,iteratedDeriv_X_succ_zero]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

lemma oddFactorial_factorial (n : ℕ) :
    (n.factorial : ℂ) * oddFactorial n * 2^n = ((2*n+1).factorial : ℂ) := by
  induction n with
  | zero => norm_num [oddFactorial]
  | succ n ih =>
    have he : 2*(n+1)+1 = (2*n+1)+1+1 := by omega
    rw [he,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,oddFactorial_succ,
      Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,pow_succ]
    push_cast
    linear_combination (2*(n:ℂ)+3)*(2*(n:ℂ)+2)*ih

lemma rootKernel_sine (t : ℂ) : t * rootKernel 0 (t^2/2) = Complex.sin t := by
  have hs := Complex.hasSum_taylorSeries_of_entire (rootKernel_differentiable 0) 0 (t^2/2)
  have hm := hs.mul_left t
  apply HasSum.unique hm
  convert Complex.hasSum_sin t using 1
  ext n
  simp only [sub_zero,smul_eq_mul,rootKernel_jets_zero]
  rw [← oddFactorial_factorial]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have ho : (oddFactorial n : ℂ) ≠ 0 := by exact_mod_cast oddFactorial_ne_zero n
  rw [div_pow,← pow_mul,pow_succ]
  field_simp

lemma rootKernel_real (Y z : ℝ) : (rootKernel Y z).im = 0 := by
  have hc : Continuous (deriv X) := by
    simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
  have hi : IntervalIntegrable
      (fun s : ℝ => deriv X ((Y:ℂ)+(z:ℂ)/2*(1-(s:ℂ)^2))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  change Complex.imCLM (∫ s : ℝ in (0)..1,
    deriv X ((Y:ℂ)+(z:ℂ)/2*(1-(s:ℂ)^2))) = 0
  rw [← Complex.imCLM.intervalIntegral_comp_comm hi]
  have he : (fun s : ℝ => (deriv X ((Y:ℂ)+(z:ℂ)/2*(1-(s:ℂ)^2))).im) =
      fun _ : ℝ => (0:ℝ) := by
    funext s
    have harg : (Y:ℂ)+(z:ℂ)/2*(1-(s:ℂ)^2) = ((Y+z/2*(1-s^2):ℝ):ℂ) := by
      push_cast
      ring
    rw [harg]
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_im_ofReal 1 (Y+z/2*(1-s^2))
  change (∫ s : ℝ in (0)..1, (deriv X ((Y:ℂ)+(z:ℂ)/2*(1-(s:ℂ)^2))).im) = 0
  rw [he]
  exact intervalIntegral.integral_zero

def characteristicIntegral (t : ℝ) (u : ℂ) : ℂ :=
  ∫ s : ℝ in (0)..1, deriv X ((t:ℂ)^2/4*(1-(s:ℂ)^2)+u*(s:ℂ)^2)

lemma characteristicIntegral_eq (t u : ℝ) :
    characteristicIntegral t u = rootKernel (u:ℂ) (((t^2-4*u)/2:ℝ):ℂ) := by
  apply intervalIntegral.integral_congr
  intro s hs
  apply congrArg (deriv X)
  push_cast
  ring

lemma characteristicIntegral_hasDerivAt (t u : ℝ) :
    HasDerivAt (characteristicIntegral t)
      (∫ s : ℝ in (0)..1, (s:ℂ)^2 * deriv (deriv X)
        ((t:ℂ)^2/4*(1-(s:ℂ)^2)+(u:ℂ)*(s:ℂ)^2)) (u:ℂ) := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  change HasDerivAt (fun w : ℂ => ∫ s : ℝ in (0)..1,
    deriv X ((t:ℂ)^2/4*(1-(s:ℂ)^2)+w*(s:ℂ)^2)) _ _
  simpa only [one_mul] using
    hasDerivAt_affineIntegral (fun _ => 1) (fun s => (t:ℂ)^2/4*(1-(s:ℂ)^2))
      (fun s => (s:ℂ)^2) continuous_const (by fun_prop) (by fun_prop) (deriv X) hg u

lemma characteristicIntegral_deriv_relation (t u : ℝ) :
    characteristicIntegral t u - ((t^2-4*u)/2:ℝ) * deriv (characteristicIntegral t) u =
      deriv X u := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  have hi : (∫ s : ℝ in (0)..1, (s:ℂ)^2 * deriv (deriv X)
      ((t:ℂ)^2/4*(1-(s:ℂ)^2)+(u:ℂ)*(s:ℂ)^2)) =
      ∫ s : ℝ in (0)..1, (s:ℂ)^2 * deriv (deriv X)
        ((u:ℂ)+((t^2-4*u)/2:ℝ)/2*(1-(s:ℂ)^2)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    apply congrArg (fun v : ℂ => (s:ℂ)^2 * deriv (deriv X) v)
    push_cast
    ring
  have hd := (characteristicIntegral_hasDerivAt t u).deriv.trans hi
  have hc := characteristicIntegral_eq t u
  exact (congrArg₂ (fun x y : ℂ => x-(((t^2-4*u)/2:ℝ):ℂ)*y) hc hd).trans
    (kernelIntegral_first_moment (deriv X) hg (u:ℂ) (((t^2-4*u)/2:ℝ):ℂ))

def weightedCharacteristic (t u : ℝ) : ℝ :=
  Real.sqrt (t^2-4*u) * (characteristicIntegral t u).re

lemma weightedCharacteristic_hasDerivAt (t u : ℝ) (hu : 0 < t^2-4*u) :
    HasDerivAt (weightedCharacteristic t) (-2*a u/Real.sqrt (t^2-4*u)) u := by
  have hq := (((hasDerivAt_id u).const_mul 4).const_sub (t^2)).sqrt (ne_of_gt hu)
  have hI := (characteristicIntegral_hasDerivAt t u).real_of_complex
  have hrel := congrArg Complex.re (characteristicIntegral_deriv_relation t u)
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hrel
  have hder : (∫ s : ℝ in (0)..1, (s:ℂ)^2 * deriv (deriv X)
      ((t:ℂ)^2/4*(1-(s:ℂ)^2)+(u:ℂ)*(s:ℂ)^2)).re =
      (deriv (characteristicIntegral t) u).re := by
    rw [(characteristicIntegral_hasDerivAt t u).deriv]
  rw [hder] at hI
  convert hq.mul hI using 1
  · rfl
  · dsimp only [id_eq]
    have hs : Real.sqrt (t^2-4*u) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
    have hs2 := Real.sq_sqrt hu.le
    field_simp
    rw [hs2]
    dsimp only [a]
    linear_combination 4*hrel

lemma weightedCharacteristic_continuous (t : ℝ) : Continuous (weightedCharacteristic t) := by
  have hc : Continuous (fun u : ℝ => (characteristicIntegral t u).re) :=
    continuous_iff_continuousAt.mpr
      (fun u => (characteristicIntegral_hasDerivAt t u).real_of_complex.continuousAt)
  unfold weightedCharacteristic
  fun_prop

lemma rootKernel_positive_zero (Y : ℝ) (hY : 0 ≤ Y)
    (ha : ∀ u ∈ Icc 0 Y, 0 < a u) :
    ∃ z : ℝ, 0 < z ∧ rootKernel Y z = 0 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (1:ℝ) (4*Y+1)/Real.pi)
  let t : ℝ := (n:ℝ)*Real.pi
  have ht : max (1:ℝ) (4*Y+1) < t := by
    exact (div_lt_iff₀ Real.pi_pos).mp hn
  have ht1 : 1 < t := lt_of_le_of_lt (le_max_left _ _) ht
  have htY : 4*Y+1 < t := lt_of_le_of_lt (le_max_right _ _) ht
  have hq : 0 < t^2-4*Y := by nlinarith
  have ht0 : 0 < t := lt_trans zero_lt_one ht1
  have hsin : Complex.sin (t:ℂ) = 0 := by
    rw [← Complex.ofReal_sin]
    simp only [t,Real.sin_nat_mul_pi,Complex.ofReal_zero]
  have hzero : rootKernel 0 ((t:ℂ)^2/2) = 0 := by
    have hs := rootKernel_sine (t:ℂ)
    rw [hsin] at hs
    exact (mul_eq_zero.mp hs).resolve_left (by exact_mod_cast ne_of_gt ht0)
  by_cases he : Y = 0
  · refine ⟨t^2/2, by positivity, ?_⟩
    subst Y
    simpa only [Complex.ofReal_zero,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_ofNat] using hzero
  have hYpos : 0 < Y := lt_of_le_of_ne hY (Ne.symm he)
  have hanti : StrictAntiOn (weightedCharacteristic t) (Icc 0 Y) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (weightedCharacteristic_continuous t).continuousOn
    intro u hu
    have hui : u ∈ Icc 0 Y := interior_subset hu
    have hqu : 0 < t^2-4*u := by linarith [hui.2]
    rw [(weightedCharacteristic_hasDerivAt t u hqu).deriv]
    exact div_neg_of_neg_of_pos (by nlinarith [ha u hui]) (Real.sqrt_pos.2 hqu)
  have hF0 : weightedCharacteristic t 0 = 0 := by
    unfold weightedCharacteristic
    rw [characteristicIntegral_eq]
    simp only [Complex.ofReal_zero,mul_zero,sub_zero,Complex.ofReal_div,
      Complex.ofReal_pow,Complex.ofReal_ofNat]
    rw [hzero]
    simp
  have hFY : weightedCharacteristic t Y < 0 := by
    have hh := hanti ⟨le_rfl,hY⟩ ⟨hY,le_rfl⟩ hYpos
    rwa [hF0] at hh
  have hKY : (rootKernel (Y:ℂ) (((t^2-4*Y)/2:ℝ):ℂ)).re < 0 := by
    rw [weightedCharacteristic,characteristicIntegral_eq] at hFY
    nlinarith only [hFY,Real.sqrt_pos.2 hq]
  have hzpos : 0 < (t^2-4*Y)/2 := by positivity
  have hK0 : 0 < (rootKernel Y 0).re := by
    rw [rootKernel_zero]
    exact ha Y ⟨hY,le_rfl⟩
  have hc : Continuous (fun z : ℝ => (rootKernel Y z).re) :=
    Complex.continuous_re.comp ((rootKernel_differentiable Y).continuous.comp Complex.continuous_ofReal)
  obtain ⟨z,hz,hroot⟩ := intermediate_value_Icc' hzpos.le hc.continuousOn
    (show (0:ℝ) ∈ Icc (rootKernel (Y:ℂ) (((t^2-4*Y)/2:ℝ):ℂ)).re (rootKernel Y 0).re
      from ⟨hKY.le,hK0.le⟩)
  refine ⟨z,lt_of_le_of_ne hz.1 ?_,?_⟩
  · intro heq
    have : z = 0 := heq.symm
    rw [this] at hroot
    exact (ne_of_gt hK0) hroot
  · apply Complex.ext
    · exact hroot
    · exact rootKernel_real Y z

end WP.Analysis
