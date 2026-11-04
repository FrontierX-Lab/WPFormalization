import WPFormalization.Analysis.HKernelUniform
import WPFormalization.Analysis.QuadraticRemainder
noncomputable section
namespace WP.Analysis
open Set
lemma barH_uniform_coefficient_bound : ∃B:ℝ,1 ≤ B ∧
    ∀Y∈Icc (0:ℝ) y₀,∀n:ℕ,1 ≤ n→|realCoeff (barH Y) n| ≤ B^n:=by
  have hcont:Continuous (fun p:Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) 1=>barH (p.1:ℝ) p.2):=by
    exact barH_joint_continuous.comp (show Continuous (fun p:Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) 1=>(p.1,(p.2:ℂ))) by fun_prop)
  obtain ⟨M,hM⟩:=isCompact_univ.bddAbove_image hcont.norm.continuousOn
  let B:=max M 1
  have hB:1 ≤ B:=le_max_right _ _
  refine ⟨B,hB,?_⟩
  intro Y hY n hn
  have hnorm:∀z∈Metric.sphere (0:ℂ) 1,‖barH Y z‖ ≤ M:=by
    intro z hz
    have hball:z∈Metric.closedBall (0:ℂ) 1:=Metric.sphere_subset_closedBall hz
    exact hM (mem_image_of_mem _ (show (⟨Y,hY⟩,⟨z,hball⟩)∈(univ:Set (Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) 1)) from mem_univ _))
  have hc:=coeff_norm_le_circle_bound (barH Y) 1 M zero_lt_one
    (barH_differentiable Y).differentiableOn hnorm n
  simp only [one_pow,div_one] at hc
  exact ((Complex.abs_re_le_norm _).trans hc).trans
    ((le_max_left _ _).trans (le_self_pow₀ hB (by omega)))
end WP.Analysis
