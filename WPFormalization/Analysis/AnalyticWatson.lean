import WPFormalization.Analysis.WatsonExpansion
import WPFormalization.Analysis.UniformTaylorRemainder
import Mathlib

/-! A single complex Cauchy circle gives a simultaneous finite Laplace
expansion at every order. Both the local Taylor remainder and the retained
polynomial tail are controlled, with no order-dependent radius or threshold.
-/
noncomputable section
namespace WP.Analysis
open MeasureTheory Set Complex Metric

lemma analytic_finite_watson_bound (g : ℂ → ℂ) (r s : ℝ) (hr : 0<r)
    (hs : 0<s) (hs1 : s≤1)
    (hg : DifferentiableOn ℂ g (Metric.closedBall 0 (2*r))) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀L:ℕ,∀ξ:ℝ,0<ξ →
      ‖ξ^s • (∫t in Ioc 0 r,(Real.exp (-(ξ*t))*t^(s-1)) • g (t:ℂ))-
        (∑j∈Finset.range L,(Real.Gamma (s+(j:ℝ))/ξ^j) • WP.coeff g j)‖≤
          C*B^L*(L.factorial:ℝ)/ξ^L := by
  obtain ⟨M₀,hM₀⟩ := (isCompact_closedBall (0:ℂ) (2*r)).exists_bound_of_continuousOn hg.continuousOn
  let M : ℝ := |M₀|+1
  have hM : 0<M := by dsimp [M];positivity
  have hMR (z : ℂ) (hz : z∈closedBall 0 (2*r)) : ‖g z‖≤M := by
    have hm := hM₀ z hz
    dsimp [M]
    linarith [le_abs_self M₀]
  have hcircle : ∀z∈Metric.sphere (0:ℂ) (2*r),‖g z‖≤M :=
    fun z hz => hMR z (Metric.sphere_subset_closedBall hz)
  have hc (j : ℕ) : ‖WP.coeff g j‖≤M/r^j := by
    apply (coeff_norm_le_circle_bound g (2*r) M (by positivity) hg hcircle j).trans
    apply div_le_div_of_nonneg_left hM.le (pow_pos hr j)
    exact pow_le_pow_left₀ hr.le (by linarith) j
  have hRealCont : ContinuousOn (fun t:ℝ => g (t:ℂ)) (Ioc 0 r) := by
    apply hg.continuousOn.comp (by fun_prop)
    intro t ht
    simp only [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
    linarith [ht.2]
  refine ⟨3*M*Real.Gamma s,2/r,by positivity,by positivity,?_⟩
  intro L ξ hξ
  have herr : ∀t∈Ioc 0 r,‖g (t:ℂ)-(∑j∈Finset.range L,t^j • WP.coeff g j)‖≤
      (2*M*(2/r)^L)*t^L := by
    intro t ht
    have ht0 : 0<t := ht.1
    have htz : ‖(t:ℂ)‖≤(2*r)/2 := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0]
      linarith [ht.2]
    have hb := complex_taylor_remainder_bound g (2*r) M (by positivity) hM.le hg hcircle L (t:ℂ) htz
    have he : (∑j∈Finset.range L,t^j • WP.coeff g j)=
        (∑j∈Finset.range L,WP.coeff g j*(t:ℂ)^j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Complex.real_smul,Complex.ofReal_pow,mul_comm]
    rw [he]
    apply hb.trans
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0]
    have hp : t/(2*r)≤(2/r)*t := by apply (div_le_iff₀ (by positivity : 0<2*r)).2;field_simp; nlinarith
    calc
      _ ≤ 2*M*(((2/r)*t)^L) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp L) (by positivity)
      _ = _ := by rw [mul_pow];ring
  have hb := finite_watson_remainder_bound (fun t:ℝ => g (t:ℂ)) (WP.coeff g) L s ξ r
    (2*M*(2/r)^L) M hs hs1 hξ hr (by positivity) hM.le
    (hRealCont.aestronglyMeasurable measurableSet_Ioc) hc herr
  apply hb.trans
  ring_nf
  exact le_rfl

lemma sqrt_laplace_integral_real_smul (α : ℂ → ℂ) (r ξ : ℝ) (hr : 0≤r) :
    (∫v in (0:ℝ)..r,Complex.exp (-(ξ:ℂ)*(v:ℂ))*
      (Real.sqrt v:ℂ)⁻¹*α (1+(v:ℂ)))=
      (∫v in Ioc (0:ℝ) r,(Real.exp (-(ξ*v))*v^((1/2:ℝ)-1)) • α (1+(v:ℂ))) := by
  rw [intervalIntegral.integral_of_le hr]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro v hv
  dsimp only
  have hv0 : 0≤v := hv.1.le
  have hrpow : v^((1/2:ℝ)-1)=(Real.sqrt v)⁻¹ := by
    rw [show (1/2:ℝ)-1=-(1/2) by ring,Real.rpow_neg hv0,←Real.sqrt_eq_rpow]
  rw [hrpow,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv]
  have he : Complex.exp (-(ξ:ℂ)*(v:ℂ))=(Real.exp (-(ξ*v)):ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he]
end WP.Analysis
