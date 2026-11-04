import Mathlib
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma sqrt_log_envelope_sublinear (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ h : ℝ, H ≤ h →
      Real.sqrt h*Real.log (h+1)+(Real.log (h+1))^2+1 ≤ ε*h := by
  have hl : Tendsto (fun x:ℝ=>Real.log x/Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have hsq : Tendsto (fun x:ℝ=>(Real.log x)^2/x) atTop (𝓝 0) := by
    have he := hl.pow 2
    simp only [zero_pow (by norm_num : (2:ℕ)≠0)] at he
    apply he.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp only [div_pow,Real.sq_sqrt hx.le]
  have hm : Tendsto (fun x:ℝ=>Real.sqrt x*Real.log x/x) atTop (𝓝 0) := by
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    apply (div_eq_div_iff hs.ne' hx.ne').mpr
    calc
      Real.log x*x = Real.log x*(Real.sqrt x)^2 := by rw [Real.sq_sqrt hx.le]
      _ = Real.sqrt x*Real.log x*Real.sqrt x := by ring
  have hi : Tendsto (fun x:ℝ=>(1:ℝ)/x) atTop (𝓝 0) := tendsto_id.const_div_atTop 1
  have ht : Tendsto (fun x:ℝ=>(Real.sqrt x*Real.log x+(Real.log x)^2+1)/x) atTop (𝓝 0) := by
    have he := (hm.add hsq).add hi
    simp only [add_zero] at he
    apply he.congr'
    exact Eventually.of_forall (fun x=>by ring)
  obtain ⟨H,hH⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (show 0<ε/2 by positivity)))
  refine ⟨max 1 H,le_max_left _ _,?_⟩
  intro h hh
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hh
  have hh0 : 0 ≤ h := by linarith
  have hlog : 0 ≤ Real.log (h+1) := Real.log_nonneg (by linarith)
  have hsmall : (Real.sqrt (h+1)*Real.log (h+1)+(Real.log (h+1))^2+1)/(h+1) < ε/2 :=
    hH (h+1) (by have he: H ≤ h := (le_max_right _ _).trans hh;linarith)
  have hsmall' := (div_lt_iff₀ (by linarith : (0:ℝ)<h+1)).mp hsmall
  have hs := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (show h ≤ h+1 by linarith)) hlog
  nlinarith only [hs,hsmall',hh1,mul_nonneg hε.le (sub_nonneg.mpr hh1)]
end WP.Analysis

namespace WP.Analysis
lemma sqrt_scale_bound (x y K : ℝ) (hK : 1 ≤ K) (hxy : x ≤ K*y) :
    Real.sqrt x ≤ K*Real.sqrt y := by
  calc
    _ ≤ Real.sqrt (K*y) := Real.sqrt_le_sqrt hxy
    _ = Real.sqrt K*Real.sqrt y := Real.sqrt_mul (by linarith : 0 ≤ K) y
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr hK)) (Real.sqrt_nonneg _)
end WP.Analysis

namespace WP.Analysis
open Set
lemma sqrt_marking_count_exponential_absorption (K α : ℝ) (hK : 0 ≤ K) (hα : 0 < α) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ g : ℝ, G ≤ g → ∀ p : ℕ,
      (p:ℝ) ≤ K*Real.sqrt g →
      (g+1)*(2:ℝ)^p*Real.exp (-α*g) ≤ Real.exp (-(α/2)*g) := by
  obtain ⟨H,hH,hlog⟩ := sqrt_log_envelope_sublinear (α/4) (by positivity)
  let x : ℝ := 4*K*Real.log 2/α
  have hx : 0 ≤ x := by dsimp [x];positivity
  refine ⟨max H (x^2+1),le_trans hH (le_max_left _ _),?_⟩
  intro g hg p hp
  have hg1 : 1 ≤ g := hH.trans ((le_max_left _ _).trans hg)
  have hg0 : 0 ≤ g := by linarith
  have hxg : x^2+1 ≤ g := (le_max_right _ _).trans hg
  have hroot : x ≤ Real.sqrt g := by nlinarith only [Real.sq_sqrt hg0,Real.sqrt_nonneg g,hxg,hx]
  have hcoef : 4*K*Real.log 2 ≤ α*Real.sqrt g := by
    have he := (div_le_iff₀ hα).mp hroot
    linarith
  have hm := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg g)
  have hm' : 4*K*Real.log 2*Real.sqrt g ≤ α*g := by
    calc
      _ ≤ α*Real.sqrt g*Real.sqrt g := hm
      _ = α*g := by rw [mul_assoc,←pow_two,Real.sq_sqrt hg0]
  have hpl : (p:ℝ)*Real.log 2 ≤ (α/4)*g := by
    have he := mul_le_mul_of_nonneg_right hp (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    nlinarith only [he,hm']
  have hlg : Real.log (g+1) ≤ (α/4)*g := by
    have he := hlog g ((le_max_left _ _).trans hg)
    have hroot1 : 1 ≤ Real.sqrt g := Real.one_le_sqrt.mpr hg1
    have hll : 0 ≤ Real.log (g+1) := Real.log_nonneg (by linarith)
    have hprod := mul_le_mul_of_nonneg_right hroot1 hll
    nlinarith only [he,hprod,sq_nonneg (Real.log (g+1))]
  have hid : (g+1)*(2:ℝ)^p*Real.exp (-α*g)=
      Real.exp (Real.log (g+1)+(p:ℝ)*Real.log 2-α*g) := by
    rw [Real.exp_sub,Real.exp_add,Real.exp_nat_mul,
      Real.exp_log (by linarith : (0:ℝ)<g+1),Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [show -α*g=-(α*g) by ring,Real.exp_neg]
    ring
  rw [hid]
  exact Real.exp_le_exp.mpr (by linarith only [hlg,hpl])
end WP.Analysis
