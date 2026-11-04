import WPFormalization.Analysis.ParameterRegular
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! The actual infimum inverse of X and the cusp profile at the origin.
Local analytic inverses agree with the original definition on full real
neighbourhoods, including at zero; all Euler origin errors are proved. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology ContDiff
lemma inverseY_eq_of_root (x Y : ℝ) (hY : Y ≤ y₀) (he : XR Y = x) : inverseY x = Y := by
  have hset : {y : ℝ | y ≤ y₀ ∧ XR y = x} = {Y} := by
    ext y
    constructor
    · intro hy
      exact mem_singleton_iff.mpr (XR_strictMonoOn.injOn hy.1 hY (hy.2.trans he.symm))
    · intro hy
      have hv := mem_singleton_iff.mp hy
      subst y
      exact ⟨hY,he⟩
  unfold inverseY
  rw [hset,csInf_singleton]
lemma inverseY_analytic_hasDerivAt_of_lt (Y : ℝ) (hY : Y < y₀) :
    AnalyticAt ℝ inverseY (XR Y) ∧ HasDerivAt inverseY (a Y)⁻¹ (XR Y) := by
  have ha := XR_analyticAt Y
  have hn : deriv XR Y ≠ 0 := by rw [(XR_hasDerivAt Y).deriv];exact (a_pos_before_y₀ Y hY).ne'
  let ψ := ha.hasStrictDerivAt.localInverse XR (deriv XR Y) Y hn
  have hψ : AnalyticAt ℝ ψ (XR Y) := ha.analyticAt_localInverse hn
  have hψ0 : ψ (XR Y) = Y := (ha.hasStrictDerivAt.eventually_left_inverse hn).self_of_nhds
  have hlt : ∀ᶠ x in 𝓝 (XR Y),ψ x < y₀ := by
    have ht : Tendsto ψ (𝓝 (XR Y)) (𝓝 Y) := by simpa only [hψ0] using hψ.continuousAt.tendsto
    exact ht.eventually (eventually_lt_nhds hY)
  have hr : ∀ᶠ x in 𝓝 (XR Y),XR (ψ x) = x := ha.hasStrictDerivAt.eventually_right_inverse hn
  have heq : ψ =ᶠ[𝓝 (XR Y)] inverseY := by
    filter_upwards [hr,hlt] with x hx hy
    exact (inverseY_eq_of_root x (ψ x) hy.le hx).symm
  refine ⟨hψ.congr heq,?_⟩
  have hd : HasDerivAt ψ (deriv XR Y)⁻¹ (XR Y) := (ha.hasStrictDerivAt.to_localInverse hn).hasDerivAt
  rw [(XR_hasDerivAt Y).deriv] at hd
  exact hd.congr_of_eventuallyEq heq.symm
lemma inverseY_analyticAt_interior (x : ℝ) (hx : x ∈ Ico 0 xCritical) : AnalyticAt ℝ inverseY x := by
  have hs := inverseY_branch x hx
  have ha := (inverseY_analytic_hasDerivAt_of_lt _ hs.1.2).1
  rwa [hs.2] at ha
lemma inverseY_hasDerivAt_interior (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    HasDerivAt inverseY (a (inverseY x))⁻¹ x := by
  have hs := inverseY_branch x hx
  have hd := (inverseY_analytic_hasDerivAt_of_lt _ hs.1.2).2
  rwa [hs.2] at hd
lemma Psi_analyticAt_interior (x : ℝ) (hx : x ∈ Ico 0 xCritical) : AnalyticAt ℝ WP.Psi x := by
  have hY := (inverseY_branch x hx).1
  exact ((density_analyticAt_interior _ hY).comp (inverseY_analyticAt_interior x hx)).div_const
lemma Psi_hasDerivAt_interior (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    HasDerivAt WP.Psi (deriv WP.density (inverseY x)/(2*a (inverseY x))) x := by
  have hY := (inverseY_branch x hx).1
  have hd := ((density_analyticAt_interior _ hY).differentiableAt.hasDerivAt.comp x
    (inverseY_hasDerivAt_interior x hx)).div_const 2
  convert! hd using 1 <;> ring
lemma Psi_deriv_pos_interior (x : ℝ) (hx : x ∈ Ico 0 xCritical) : 0 < deriv WP.Psi x := by
  rw [(Psi_hasDerivAt_interior x hx).deriv]
  have hY := (inverseY_branch x hx).1
  exact div_pos (density_deriv_pos_interior _ hY) (mul_pos (by norm_num) (a_pos _ hY))
lemma Psi_strictMonoOn : StrictMonoOn WP.Psi (Ioo 0 xCritical) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 xCritical)
  · intro x hx
    exact (Psi_analyticAt_interior x ⟨hx.1.le,hx.2⟩).continuousAt.continuousWithinAt
  · intro x hx
    have hm : x ∈ Ioo 0 xCritical := interior_subset hx
    exact Psi_deriv_pos_interior x ⟨hm.1.le,hm.2⟩
lemma xCritical_pos_parameter : 0 < xCritical := by
  change 0 < XR y₀
  rw [XR_eq_neg_mul_second]
  apply mul_pos y₀_pos
  exact neg_pos.mpr (second_X_neg_before y₀ (by linarith [y₀_lt_three_halves]))
lemma inverseY_zero_value : inverseY 0 = 0 :=
  inverseY_eq_of_root 0 0 y₀_pos.le XR_zero
lemma Psi_zero_value : WP.Psi 0 = 0 := by
  simp only [WP.Psi,inverseY_zero_value,WP.density_zero_value,zero_div]
lemma Psi_deriv_zero_value : deriv WP.Psi 0 = 2 := by
  rw [(Psi_hasDerivAt_interior 0 ⟨le_rfl,xCritical_pos_parameter⟩).deriv,
    inverseY_zero_value,WP.a_zero,density_deriv_zero_value]
  norm_num
lemma euler_analyticAt {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) : AnalyticAt ℝ (WP.euler f) 0 :=
  analyticAt_id.mul hf.deriv
lemma euler_deriv_zero {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) : deriv (WP.euler f) 0 = deriv f 0 := by
  have hd : HasDerivAt (WP.euler f) (deriv f 0) 0 := by
    simpa only [WP.euler,id_eq,Pi.mul_apply,zero_mul,one_mul,add_zero] using!
      (hasDerivAt_id (0:ℝ)).mul hf.deriv.differentiableAt.hasDerivAt
  exact hd.deriv
lemma Psi_origin_analytic :
    AnalyticAt ℝ WP.Psi 0 ∧ AnalyticAt ℝ (WP.euler WP.Psi) 0 ∧
      AnalyticAt ℝ (WP.euler (WP.euler WP.Psi)) 0 := by
  have ha := Psi_analyticAt_interior 0 ⟨le_rfl,xCritical_pos_parameter⟩
  exact ⟨ha,euler_analyticAt ha,euler_analyticAt (euler_analyticAt ha)⟩
lemma Psi_origin_errors : ∀ j ∈ Finset.range 3,
    (fun x => (WP.euler^[j]) WP.Psi x-2*x) =O[𝓝[>] (0:ℝ)] (fun x => x^2) := by
  have hP := Psi_origin_analytic.1
  have hE := Psi_origin_analytic.2.1
  have hEE := Psi_origin_analytic.2.2
  have hEd : deriv (WP.euler WP.Psi) 0 = 2 := by rw [euler_deriv_zero hP,Psi_deriv_zero_value]
  have hEEd : deriv (WP.euler (WP.euler WP.Psi)) 0 = 2 := by rw [euler_deriv_zero hE,hEd]
  have hE0 : WP.euler WP.Psi 0 = 0 := by simp only [WP.euler,zero_mul]
  have hEE0 : WP.euler (WP.euler WP.Psi) 0 = 0 := by simp only [WP.euler,zero_mul]
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · simpa only [Function.iterate_zero_apply,Psi_zero_value,Psi_deriv_zero_value,sub_zero] using
      (analytic_first_order_error_at_zero WP.Psi hP).mono nhdsWithin_le_nhds
  · simpa only [Function.iterate_one,hE0,hEd,sub_zero] using
      (analytic_first_order_error_at_zero (WP.euler WP.Psi) hE).mono nhdsWithin_le_nhds
  · simpa only [Function.iterate_succ_apply,Function.iterate_zero_apply,hEE0,hEEd,sub_zero] using
      (analytic_first_order_error_at_zero (WP.euler (WP.euler WP.Psi)) hEE).mono nhdsWithin_le_nhds


end WP.Analysis
