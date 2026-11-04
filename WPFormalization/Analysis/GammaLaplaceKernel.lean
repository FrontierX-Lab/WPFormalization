import WPFormalization.External.GammaLaplace
import WPFormalization.Analysis.Taylor
import WPFormalization.HigherOrder.EndpointFormal

/-! The actual removable complex germ of the classical Gamma-ratio Laplace kernel. The raw real quotient has a different totalized value at zero; equality is asserted only for positive real t. The germ construction and analyticity are proved with Mathlib, independently of the deferred integral identity. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

def complexExpUnit (z : ℂ) : ℂ := dslope Complex.exp 0 z
@[simp] lemma complexExpUnit_zero : complexExpUnit 0=1 := by
  rw [complexExpUnit,dslope_same,Complex.deriv_exp]
  simp
@[fun_prop] lemma complexExpUnit_analytic (z : ℂ) : AnalyticAt ℂ complexExpUnit z := by
  have hd : AnalyticOnNhd ℂ complexExpUnit univ :=
    ((Complex.differentiableOn_dslope (by simp : (univ:Set ℂ)∈𝓝 (0:ℂ))).mpr
      Complex.differentiable_exp.differentiableOn).analyticOnNhd isOpen_univ
  exact hd z (mem_univ _)
lemma complexExpUnit_eq (z : ℂ) (hz : z≠0) : complexExpUnit z=(Complex.exp z-1)/z := by
  rw [complexExpUnit,dslope_of_ne Complex.exp hz]
  simp only [slope,sub_zero,vsub_eq_sub,smul_eq_mul,Complex.exp_zero]
  ring

def gammaRatioQuotient (a : ℝ) (z : ℂ) : ℂ :=
  (a:ℂ)*complexExpUnit (-(a:ℂ)*z)/complexExpUnit (-z)
@[simp] lemma gammaRatioQuotient_zero (a : ℝ) : gammaRatioQuotient a 0=(a:ℂ) := by
  simp [gammaRatioQuotient]
lemma gammaRatioQuotient_analytic_zero (a : ℝ) : AnalyticAt ℂ (gammaRatioQuotient a) 0 := by
  unfold gammaRatioQuotient
  fun_prop (disch := simp)

def gammaRatioKernel (a : ℝ) (z : ℂ) : ℂ := -dslope (gammaRatioQuotient a) 0 z
lemma gammaRatioKernel_analytic_zero (a : ℝ) : AnalyticAt ℂ (gammaRatioKernel a) 0 := by
  obtain ⟨p,hp⟩ := gammaRatioQuotient_analytic_zero a
  exact hp.has_fpower_series_dslope_fslope.analyticAt.neg
lemma gammaRatioQuotient_eq (a : ℝ) (ha : a≠0) (z : ℂ) (hz : z≠0)
    (hd : Complex.exp (-z)≠1) :
    gammaRatioQuotient a z=(1-Complex.exp (-(a:ℂ)*z))/(1-Complex.exp (-z)) := by
  have haC : (a:ℂ)≠0 := by exact_mod_cast ha
  unfold gammaRatioQuotient
  rw [complexExpUnit_eq _ (mul_ne_zero (neg_ne_zero.mpr haC) hz),
    complexExpUnit_eq _ (neg_ne_zero.mpr hz)]
  have hd' : Complex.exp (-z)-1≠0 := sub_ne_zero.mpr hd
  have hd'' : 1-Complex.exp (-z)≠0 := sub_ne_zero.mpr hd.symm
  field_simp [haC,hz,hd',hd''] <;> ring
lemma gammaRatioKernel_eq (a : ℝ) (ha : a≠0) (z : ℂ) (hz : z≠0)
    (hd : Complex.exp (-z)≠1) :
    gammaRatioKernel a z=((a:ℂ)-(1-Complex.exp (-(a:ℂ)*z))/(1-Complex.exp (-z)))/z := by
  rw [gammaRatioKernel,dslope_of_ne (gammaRatioQuotient a) hz]
  simp only [slope,sub_zero,vsub_eq_sub,smul_eq_mul,gammaRatioQuotient_zero]
  rw [gammaRatioQuotient_eq a ha z hz hd]
  ring
lemma gammaRatioKernel_real (a t : ℝ) (ha : 0<a) (ht : 0<t) :
    gammaRatioKernel a (t:ℂ)=(External.gammaLogRatioKernel a t:ℂ) := by
  have hne : (t:ℂ)≠0 := by exact_mod_cast ht.ne'
  have hex : Complex.exp (-(t:ℂ))≠1 := by
    have he : Real.exp (-t)<1 := Real.exp_lt_one_iff.mpr (by linarith)
    intro hc
    have hr := congrArg Complex.re hc
    simp only [←Complex.ofReal_neg,Complex.exp_ofReal_re,Complex.one_re] at hr
    linarith
  rw [gammaRatioKernel_eq a ha.ne' (t:ℂ) hne hex]
  unfold External.gammaLogRatioKernel
  push_cast
  rfl
end WP.Analysis
