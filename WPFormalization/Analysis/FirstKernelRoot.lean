import WPFormalization.Analysis.CriticalKernelLimits
import Mathlib.Topology.Maps.Proper.Basic
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma K_joint_continuous : Continuous (fun p : ℂ × ℂ => K p.1 p.2) := by
  simpa only [K,one_mul] using kernelIntegral_continuous_joint (fun _ => 1) continuous_const (deriv X) (X_differentiable.deriv.continuous)
lemma K_deriv_integral (Y z : ℂ) : deriv (K Y) z = ∫ s : ℝ in (0)..1,
    ((1-(s : ℂ)^2)/2)*deriv (deriv X) (Y+z/2*(1-(s : ℂ)^2)) := by
  have hg : Differentiable ℂ (deriv X) := by simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  have heq : K Y = fun w => ∫ s : ℝ in (0)..1, (1 : ℂ)*deriv X (Y+w/2*(1-(s : ℂ)^2)) := by funext w; simp only [K,one_mul]
  rw [heq]
  simpa only [one_mul] using (hasDerivAt_kernelIntegral (fun _ => 1) continuous_const (deriv X) hg Y z).deriv
lemma K_deriv_re_neg_interval (Y z : ℝ) (hY : 0 ≤ Y) (hz : 0 ≤ z)
    (htop : Y+z/2 ≤ Real.pi^2/4) : (deriv (K Y) z).re < 0 := by
  let f (s : ℝ) : ℂ := ((1-(s:ℂ)^2)/2)*deriv (deriv X) ((Y:ℂ)+(z:ℂ)/2*(1-(s:ℂ)^2))
  have hc : Continuous f := by
    have hg : Continuous (deriv (deriv X)) := by simpa only [iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using (iteratedDeriv_X_differentiable 2).continuous
    dsimp [f]
    fun_prop
  have hf (s : ℝ) : (f s).re = ((1-s^2)/2)*(iteratedDeriv 2 X ((Y+z/2*(1-s^2):ℝ):ℂ)).re := by
    have he : f s = (((1-s^2)/2:ℝ):ℂ)*iteratedDeriv 2 X ((Y+z/2*(1-s^2):ℝ):ℂ) := by
      dsimp [f]
      push_cast
      simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
    ring
  have harg (s : ℝ) (hs : s ∈ Icc 0 1) : Y+z/2*(1-s^2) ∈ Icc 0 (Real.pi^2/4) := by
    have hs2 : s^2 ≤ 1 := by nlinarith [hs.1,hs.2]
    constructor
    · nlinarith [mul_nonneg hz (sub_nonneg.mpr hs2)]
    · nlinarith [mul_nonneg hz (sq_nonneg s)]
  have hh := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num : (0:ℝ)<1)
    (Complex.continuous_re.comp hc).continuousOn continuous_const.continuousOn
    (g := fun _ => (0:ℝ)) (fun s hs => by
      change (f s).re ≤ 0
      rw [hf]
      have hs2 : s^2≤1 := by nlinarith [hs.1,hs.2]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith)
        ((bessel_signs_pi_interval.2.1 _ (harg s ⟨hs.1.le,hs.2⟩)).1.le))
    ⟨0,by norm_num,by
      change (f 0).re < 0
      rw [hf]
      have hh := (bessel_signs_pi_interval.2.1 _ (harg 0 (by norm_num))).1
      norm_num at hh ⊢
      linarith⟩
  rw [intervalIntegral.integral_zero] at hh
  rw [K_deriv_integral]
  change (∫ s : ℝ in (0)..1, f s).re < 0
  change RCLike.re (∫ s : ℝ in (0)..1, f s) < 0
  rw [← intervalIntegral.intervalIntegral_re (hc.intervalIntegrable 0 1)]
  exact hh
lemma K_strictAntiOn_interval (Y : ℝ) (hY : 0 ≤ Y) :
    StrictAntiOn (fun z : ℝ => (K Y z).re) (Icc 0 ((Real.pi^2-4*Y)/2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (Complex.continuous_re.comp ((K_differentiable Y).continuous.comp Complex.continuous_ofReal)).continuousOn
  intro z hz
  have hzi : z ∈ Icc 0 ((Real.pi^2-4*Y)/2) := interior_subset hz
  change deriv (fun z:ℝ => (K Y z).re) z < 0
  rw [((K_differentiable Y z).hasDerivAt.real_of_complex).deriv]
  exact K_deriv_re_neg_interval Y z hY hzi.1 (by linarith [hzi.2])
lemma r_le_pi (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : r Y ≤ (Real.pi^2-4*Y)/2 := by
  let t := Real.pi
  have hq : 0 < t^2-4*Y := by
    have h := y₀_lt_three_halves
    have hp := Real.pi_gt_three
    dsimp [t]
    nlinarith [hY.2]
  have hzero : rootKernel 0 ((t:ℂ)^2/2) = 0 := by
    have hs := rootKernel_sine (t:ℂ)
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [show Complex.sin (t:ℂ)=0 by simp [t,← Complex.ofReal_sin]] at hs
    exact (mul_eq_zero.mp hs).resolve_left ht0
  by_cases he : Y=0
  · subst Y
    simp only [mul_zero,sub_zero]
    apply r_le_of_K_zero 0 (Real.pi^2/2) (by positivity)
    simpa only [t,K,rootKernel,Complex.ofReal_zero,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat] using hzero
  have hYpos : 0<Y := lt_of_le_of_ne hY.1 (Ne.symm he)
  have hanti : StrictAntiOn (weightedCharacteristic t) (Icc 0 Y) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (weightedCharacteristic_continuous t).continuousOn
    intro u hu
    have hui : u ∈ Icc 0 Y := interior_subset hu
    have hqu : 0<t^2-4*u := by linarith [hui.2]
    rw [(weightedCharacteristic_hasDerivAt t u hqu).deriv]
    exact div_neg_of_neg_of_pos (by nlinarith [a_pos u ⟨hui.1,lt_of_le_of_lt hui.2 hY.2⟩]) (Real.sqrt_pos.2 hqu)
  have hF0 : weightedCharacteristic t 0=0 := by
    unfold weightedCharacteristic
    rw [characteristicIntegral_eq]
    simp only [Complex.ofReal_zero,mul_zero,sub_zero,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat]
    rw [hzero]
    simp
  have hFY : weightedCharacteristic t Y<0 := by
    have hh := hanti ⟨le_rfl,hY.1⟩ ⟨hY.1,le_rfl⟩ hYpos
    rwa [hF0] at hh
  have hKY : (K Y (((t^2-4*Y)/2:ℝ):ℂ)).re<0 := by
    rw [weightedCharacteristic,characteristicIntegral_eq] at hFY
    change Real.sqrt (t^2-4*Y)*(K Y (((t^2-4*Y)/2:ℝ):ℂ)).re<0 at hFY
    nlinarith only [hFY,Real.sqrt_pos.2 hq]
  have hzpos : 0<(t^2-4*Y)/2 := by positivity
  have hK0 : 0<(K Y 0).re := by simpa [K_zero,derivX_ofReal] using a_pos Y hY
  have hc : Continuous (fun z:ℝ => (K Y z).re) := Complex.continuous_re.comp ((K_differentiable Y).continuous.comp Complex.continuous_ofReal)
  obtain ⟨z,hz,hroot⟩ := intermediate_value_Icc' hzpos.le hc.continuousOn
    (show (0:ℝ) ∈ Icc (K Y (((t^2-4*Y)/2:ℝ):ℂ)).re (K Y 0).re from ⟨hKY.le,hK0.le⟩)
  have hzp : 0<z := lt_of_le_of_ne hz.1 (by intro he; rw [← he] at hroot; exact (ne_of_gt hK0) hroot)
  have hrootc : K Y z=0 := by
    apply Complex.ext
    · exact hroot
    · exact rootKernel_real Y z
  exact (r_le_of_K_zero Y z hzp hrootc).trans hz.2
lemma K_deriv_at_r_re_neg (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : (deriv (K Y) (r Y)).re<0 :=
  K_deriv_re_neg_interval Y (r Y) hY.1 (r_pos Y hY).le (by linarith [r_le_pi Y hY])
lemma K_zero_unique_interval (Y z : ℝ) (hY : Y ∈ Ico 0 y₀)
    (hz : z ∈ Icc 0 ((Real.pi^2-4*Y)/2)) (hroot : K Y z=0) : z=r Y := by
  apply (K_strictAntiOn_interval Y hY.1).injOn hz ⟨(r_pos Y hY).le,r_le_pi Y hY⟩
  simp only [hroot,K_r_zero Y hY]
lemma K_deriv_at_r_ne_zero (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : deriv (K Y) (r Y) ≠ 0 := by
  intro he
  have h := K_deriv_at_r_re_neg Y hY
  rw [he] at h
  exact (lt_irrefl 0) h
lemma r_continuous_interior : Continuous (fun Y : Ico 0 y₀ => r (Y:ℝ)) := by
  let F : Ico 0 y₀ → Icc (0:ℝ) (Real.pi^2/2) := fun Y =>
    ⟨r Y, (r_pos Y Y.property).le, (r_le_pi Y Y.property).trans (by linarith [Y.property.1])⟩
  have hF : Continuous F := by
    apply continuous_of_isClosed_graph
    have he : Function.graph F = {p | K (p.1:ℝ) (p.2:ℝ) = 0} ∩
        {p | (p.1:ℝ)+(p.2:ℝ)/2 ≤ Real.pi^2/4} := by
      ext p
      constructor
      · intro hp
        change F p.1 = p.2 at hp
        have hev : r (p.1:ℝ) = (p.2:ℝ) := congrArg Subtype.val hp
        change K (p.1:ℝ) (p.2:ℝ)=0 ∧ (p.1:ℝ)+(p.2:ℝ)/2≤Real.pi^2/4
        rw [← hev]
        exact ⟨K_r_zero p.1 p.1.property,by linarith [r_le_pi p.1 p.1.property]⟩
      · rintro ⟨hp,hbound⟩
        change (p.1:ℝ)+(p.2:ℝ)/2 ≤ Real.pi^2/4 at hbound
        change K (p.1:ℝ) (p.2:ℝ)=0 at hp
        change F p.1 = p.2
        apply Subtype.ext
        exact (K_zero_unique_interval p.1 p.2 p.1.property ⟨p.2.property.1,by linarith⟩ hp).symm
    rw [he]
    apply IsClosed.inter
    · have hc : Continuous (fun p : Ico (0:ℝ) y₀ × Icc (0:ℝ) (Real.pi^2/2) => (((p.1:ℝ):ℂ),((p.2:ℝ):ℂ))) := by fun_prop
      exact isClosed_eq (K_joint_continuous.comp hc) continuous_const
    · exact isClosed_le (by fun_prop) continuous_const
  exact continuous_subtype_val.comp hF
end WP.Analysis
