import WPFormalization.Analysis.ImplicitBranch
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! Actual analytic factors at a simple zero, removable quotients, and the
analyticity of the positive real square root, proved using Mathlib. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology ContDiff
lemma analytic_factor_at_zero (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) (h0 : f 0 = 0) :
    ∃ F : ℝ → ℝ,AnalyticAt ℝ F 0 ∧ F 0 = deriv f 0 ∧ ∀ᶠ z in 𝓝 0,f z = z*F z := by
  obtain ⟨F,hF,he⟩ := hf.exists_eventuallyEq_sum_add_pow_mul 1
  simp only [Finset.sum_range_one,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,
    one_smul,iteratedDeriv_zero,h0,zero_add,pow_one,smul_eq_mul,one_mul,zero_add] at he
  have hd : HasDerivAt (fun z : ℝ => z*F z) (F 0) 0 := by
    simpa only [id_eq,Pi.mul_apply,zero_mul,one_mul,zero_add,add_zero] using!
      (hasDerivAt_id (0:ℝ)).mul hF.differentiableAt.hasDerivAt
  exact ⟨F,hF,(hd.congr_of_eventuallyEq he).deriv.symm,he⟩
lemma analytic_removable_ratio_at_zero (f g : ℝ → ℝ)
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hg' : deriv g 0 ≠ 0) :
    ∃ R : ℝ → ℝ,AnalyticAt ℝ R 0 ∧ R 0 = deriv f 0/deriv g 0 ∧
      ∀ᶠ z in 𝓝 0,z ≠ 0 → f z/g z = R z := by
  obtain ⟨F,hF,hF0,hfe⟩ := analytic_factor_at_zero f hf hf0
  obtain ⟨G,hG,hG0,hge⟩ := analytic_factor_at_zero g hg hg0
  refine ⟨fun z => F z/G z,hF.div hG (by rwa [hG0]),?_,?_⟩
  · dsimp only
    rw [hF0,hG0]
  · filter_upwards [hfe,hge] with z hfz hgz hz
    rw [hfz,hgz,mul_div_mul_left _ _ hz]
lemma sqrt_analyticAt_of_pos (x : ℝ) (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x := by
  let F (p : ℂ × ℂ) : ℂ := p.2^2-p.1
  have hc : ContDiff ℂ 1 F := by dsimp [F];fun_prop
  have hInv : (fderiv ℂ F ((x:ℂ),(Real.sqrt x:ℂ)) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    apply complex_clm_isInvertible_of_apply_one_ne_zero
    have hd := ((hc.differentiable (by norm_num) ((x:ℂ),(Real.sqrt x:ℂ))).hasFDerivAt.comp
      (Real.sqrt x:ℂ) (hasFDerivAt_prodMk_right (x:ℂ) (Real.sqrt x:ℂ))).hasDerivAt
    have he : HasDerivAt (fun t : ℂ => F ((x:ℂ),t)) (2*(Real.sqrt x:ℂ)) (Real.sqrt x:ℂ) := by
      simpa only [F,pow_one,mul_one,id_eq,Pi.pow_apply,show 2-1 = (1:ℕ) by omega] using! ((hasDerivAt_id (Real.sqrt x:ℂ)).pow 2).sub_const (x:ℂ)
    rw [hd.unique he]
    apply mul_ne_zero (by norm_num)
    exact_mod_cast (Real.sqrt_pos.mpr hx).ne'
  apply analyticAt_real_implicit_continuous_branch F Real.sqrt x hc.contDiffAt hInv
    Real.continuous_sqrt.continuousAt
  have hbase : F ((x:ℂ),(Real.sqrt x:ℂ)) = 0 := by
    change (Real.sqrt x:ℂ)^2-(x:ℂ) = 0
    exact_mod_cast sub_eq_zero.mpr (Real.sq_sqrt hx.le)
  filter_upwards [eventually_gt_nhds hx] with y hy
  rw [hbase]
  change (Real.sqrt y:ℂ)^2-(y:ℂ) = 0
  exact_mod_cast sub_eq_zero.mpr (Real.sq_sqrt hy.le)

end WP.Analysis
