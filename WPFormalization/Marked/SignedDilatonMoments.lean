import WPFormalization.Marked.DilatonMoments
import WPFormalization.Analysis.HarmonicProbability
/-! Exact first and second signed moments of the canonical dilaton coefficients,
proved by the entire Taylor series and the normalized kernel identity at one. -/
noncomputable section
open Set
namespace WP
lemma entire_realCoeff_hasSum (f : ℂ→ℂ) (hf : Differentiable ℂ f) :
    HasSum (realCoeff f) (f 1).re := by
  have hs := Complex.hasSum_taylorSeries_of_entire hf 0 1
  have hsc : HasSum (fun n => coeff f n) (f 1) := by
    convert! hs using 1
    ext n
    simp only [coeff,sub_zero,one_pow,smul_eq_mul]
    ring
  change HasSum (fun n => (coeff f n).re) (f 1).re
  simpa only [Complex.reCLM_apply] using hsc.mapL Complex.reCLM

lemma entire_euler_realCoeff_hasSum (f : ℂ→ℂ) (hf : Differentiable ℂ f) :
    HasSum (fun n : ℕ => (n:ℝ)*realCoeff f n) (deriv f 1).re := by
  have hd : Differentiable ℂ (fun z : ℂ => z*deriv f z) := by
    intro z
    exact differentiableAt_id.mul ((hf.analyticAt z).deriv.differentiableAt)
  have hs := entire_realCoeff_hasSum _ hd
  convert! hs using 1
  · ext n
    simp only [realCoeff]
    rw [Analysis.harmonic_coeff_euler f (hf.analyticAt 0) n]
    simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,realCoeff]
  · simp only [one_mul]

lemma canonicalDilatonCoefficient_succ_first_hasSum_raw (Y : ℝ) :
    HasSum (fun n : ℕ => ((n:ℝ)+1)*canonicalDilatonCoefficient Y (n+1))
      (((deriv (barH Y) 1).re+(barH Y 1).re)/3) := by
  have hs := (entire_euler_realCoeff_hasSum (barH Y) (barH_differentiable Y)).add
    (entire_realCoeff_hasSum (barH Y) (barH_differentiable Y))
  convert! hs.div_const 3 using 1
  ext n
  simp only [canonicalDilatonCoefficient,show 1≤n+1 by omega,if_pos,Nat.add_sub_cancel]
  ring

lemma barH_deriv_one (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    deriv (barH Y) 1=-(3/2:ℂ)*barH Y 1 := by
  have hd := normalized_kernel_identity Y hY 1
  rw [Analysis.barK_one_zero Y hY] at hd
  linear_combination -(3/2:ℂ)*hd

lemma canonicalDilatonCoefficient_first_hasSum (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    HasSum (fun d : ℕ => (d:ℝ)*canonicalDilatonCoefficient Y d) (-(A Y)/2) := by
  have hs := canonicalDilatonCoefficient_succ_first_hasSum_raw Y
  rw [barH_deriv_one Y hY] at hs
  have hs' : HasSum (fun n : ℕ => ((n:ℝ)+1)*canonicalDilatonCoefficient Y (n+1)) (-(A Y)/2) := by
    convert! hs using 1
    norm_num [Complex.mul_re,A]
    <;>ring
  have ht := (hasSum_nat_add_iff (f := fun d : ℕ => (d:ℝ)*canonicalDilatonCoefficient Y d) 1).mp
    (by simpa only [Nat.cast_add,Nat.cast_one] using hs')
  simpa only [Finset.sum_range_one,Nat.cast_zero,zero_mul,add_zero] using ht

lemma entire_euler_squared_realCoeff_hasSum (f : ℂ→ℂ) (hf : Differentiable ℂ f) :
    HasSum (fun n : ℕ => (n:ℝ)^2*realCoeff f n)
      (deriv f 1+deriv (deriv f) 1).re := by
  have hd : Differentiable ℂ (fun z : ℂ => z*deriv f z) := by
    intro z
    exact differentiableAt_id.mul ((hf.analyticAt z).deriv.differentiableAt)
  have hs := entire_euler_realCoeff_hasSum _ hd
  have he : deriv (fun z : ℂ => z*deriv f z) 1=deriv f 1+deriv (deriv f) 1 := by
    have ht := (hasDerivAt_id (1:ℂ)).mul ((hf.analyticAt 1).deriv.differentiableAt.hasDerivAt)
    have hfun : id*deriv f=(fun z : ℂ => z*deriv f z) := by ext z;rfl
    rw [hfun] at ht
    simpa only [id_eq,one_mul,mul_one,add_comm] using ht.deriv
  rw [he] at hs
  convert! hs using 1
  ext n
  simp only [realCoeff]
  rw [Analysis.harmonic_coeff_euler f (hf.analyticAt 0) n]
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  ring
lemma canonicalDilatonCoefficient_succ_second_hasSum_raw (Y : ℝ) :
    HasSum (fun n : ℕ => ((n:ℝ)+1)^2*canonicalDilatonCoefficient Y (n+1))
      (((deriv (deriv (barH Y)) 1).re+3*(deriv (barH Y) 1).re+(barH Y 1).re)/3) := by
  have hs := ((entire_euler_squared_realCoeff_hasSum (barH Y) (barH_differentiable Y)).add
    ((entire_euler_realCoeff_hasSum (barH Y) (barH_differentiable Y)).mul_left 2)).add
    (entire_realCoeff_hasSum (barH Y) (barH_differentiable Y))
  convert! hs.div_const 3 using 1
  · ext n
    simp only [canonicalDilatonCoefficient,show 1≤n+1 by omega,ite_true,Nat.add_sub_cancel]
    ring
  · simp only [Complex.add_re]
    ring
lemma canonicalDilatonCoefficient_second_hasSum (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    HasSum (fun d : ℕ => (d:ℝ)^2*canonicalDilatonCoefficient Y d)
      ((deriv (deriv (barH Y)) 1).re/3-7*A Y/2) := by
  have hs := canonicalDilatonCoefficient_succ_second_hasSum_raw Y
  rw [barH_deriv_one Y hY] at hs
  have hs' : HasSum (fun n : ℕ => ((n:ℝ)+1)^2*canonicalDilatonCoefficient Y (n+1))
      ((deriv (deriv (barH Y)) 1).re/3-7*A Y/2) := by
    convert! hs using 1
    norm_num [Complex.mul_re,A]
    <;>ring
  have ht := (hasSum_nat_add_iff (f := fun d : ℕ => (d:ℝ)^2*canonicalDilatonCoefficient Y d) 1).mp
    (by simpa only [Nat.cast_add,Nat.cast_one] using hs')
  simpa only [Finset.sum_range_one,Nat.cast_zero,zero_pow (by omega : 2≠0),zero_mul,add_zero] using ht
end WP
