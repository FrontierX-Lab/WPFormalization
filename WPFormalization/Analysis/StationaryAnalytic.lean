import WPFormalization.Statements.ParameterDefinitions
import WPFormalization.Analysis.StationaryQ
import WPFormalization.Analysis.ImplicitBranch

/-! Analyticity of the original infimum-defined T, including its negative-Y
neighborhood at zero. On the open domain the intermediate-value root equals
the original sInf. Its closed graph in a fixed compact interval gives actual
continuity. The complex C¹ implicit theorem then identifies the analytic
branch with that same real function, without changing its definition.
-/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma T_eq_stationaryParameterDomain_root (Y t : ℝ) (hY : Y ∈ stationaryParameterDomain)
    (ht : t ∈ Ioo y₀ (5/2 : ℝ)) (hzero : stationaryQReal Y t = 0) : WP.T Y = t := by
  let S := {v : ℝ | y₀ < v ∧ (∫ w in Y..v,a w/Real.sqrt (v-w)) = 0}
  have hmem : t ∈ S := by
    refine ⟨ht.1,?_⟩
    rw [stationaryIntegral_eq_stationaryQReal Y t (lt_trans hY.1 ht.1),hzero,mul_zero]
  have hlower : ∀ v ∈ S,t ≤ v := by
    intro v hv
    by_contra h
    have hvt : v < t := lt_of_not_ge h
    have hq : stationaryQReal Y v = 0 := by
      have hi := hv.2
      rw [stationaryIntegral_eq_stationaryQReal Y v (lt_trans hY.1 hv.1)] at hi
      exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (mul_pos (by norm_num)
        (Real.sqrt_pos.mpr (sub_pos.mpr (lt_trans hY.1 hv.1)))))
    have hanti := stationaryQ_strictAntiOn_T Y hY.1
    have he := hanti ⟨hv.1.le,le_trans hvt.le ht.2.le⟩ ⟨ht.1.le,ht.2.le⟩ hvt
    change stationaryQReal Y t < stationaryQReal Y v at he
    rw [hzero,hq] at he
    exact lt_irrefl _ he
  have hB : BddBelow S := ⟨t,hlower⟩
  have hinf : sInf S = t := le_antisymm (csInf_le hB hmem) (le_csInf ⟨_,hmem⟩ hlower)
  unfold WP.T
  rw [if_neg (ne_of_lt hY.1)]
  exact hinf
lemma T_root_on_stationaryParameterDomain (Y : ℝ) (hY : Y ∈ stationaryParameterDomain) :
    WP.T Y ∈ Ioo y₀ (5/2 : ℝ) ∧ stationaryQReal Y (WP.T Y) = 0 := by
  obtain ⟨t,ht,hzero⟩ := stationaryParameterDomain_exists_root Y hY
  rw [T_eq_stationaryParameterDomain_root Y t hY ht hzero]
  exact ⟨ht,hzero⟩

lemma T_continuousOn_stationaryParameterDomain : ContinuousOn WP.T stationaryParameterDomain := by
  let F : stationaryParameterDomain → Icc y₀ (5/2 : ℝ) := fun Y =>
    ⟨WP.T Y,(T_root_on_stationaryParameterDomain Y Y.property).1.1.le,
      (T_root_on_stationaryParameterDomain Y Y.property).1.2.le⟩
  have hF : Continuous F := by
    apply continuous_of_isClosed_graph
    have he : Function.graph F = {p : stationaryParameterDomain × Icc y₀ (5/2 : ℝ) |
        stationaryQReal p.1 p.2 = 0} := by
      ext p
      constructor
      · intro hp
        change F p.1 = p.2 at hp
        have hv := congrArg Subtype.val hp
        change stationaryQReal p.1 p.2 = 0
        rw [← hv]
        exact (T_root_on_stationaryParameterDomain p.1 p.1.property).2
      · intro hp
        change F p.1 = p.2
        apply Subtype.ext
        have hs := T_root_on_stationaryParameterDomain p.1 p.1.property
        apply (stationaryQ_strictAntiOn_T p.1 p.1.property.1).injOn
          ⟨hs.1.1.le,hs.1.2.le⟩ p.2.property
        change stationaryQReal p.1 (WP.T p.1) = stationaryQReal p.1 p.2
        rw [hs.2,hp]
    rw [he]
    have hp : Continuous (fun p : stationaryParameterDomain × Icc y₀ (5/2 : ℝ) =>
        ((p.1 : ℝ),(p.2 : ℝ))) := by fun_prop
    have hc : Continuous (fun p : stationaryParameterDomain × Icc y₀ (5/2 : ℝ) =>
        stationaryQReal p.1 p.2) := by
      simpa only [Function.comp_def] using stationaryQReal_joint_continuous.comp hp
    exact isClosed_eq hc continuous_const
  exact continuousOn_iff_continuous_restrict.mpr (continuous_subtype_val.comp hF)
lemma T_continuousAt_on_stationaryParameterDomain (Y : ℝ) (hY : Y ∈ stationaryParameterDomain) :
    ContinuousAt WP.T Y :=
  (T_continuousOn_stationaryParameterDomain Y hY).continuousAt (stationaryParameterDomain_isOpen.mem_nhds hY)
lemma stationaryQ_im_real (Y T : ℝ) : (stationaryQProd ((Y : ℂ),(T : ℂ))).im = 0 := by
  rw [stationaryQ_eq_K]
  have he : 2*((T : ℂ)-(Y : ℂ)) = ((2*(T-Y) : ℝ) : ℂ) := by push_cast; ring
  rw [he]
  exact rootKernel_real Y (2*(T-Y))
lemma stationaryQ_zero_of_real_zero (Y T : ℝ) (h : stationaryQReal Y T = 0) :
    stationaryQProd ((Y : ℂ),(T : ℂ)) = 0 := by
  apply Complex.ext
  · exact h
  · exact stationaryQ_im_real Y T
lemma stationaryQ_partial_one (Y T : ℂ) :
    (fderiv ℂ stationaryQProd (Y,T) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) 1 =
      2*deriv (K Y) (2*(T-Y)) := by
  have hf := (stationaryQ_contDiff_one.differentiable (by norm_num) (Y,T)).hasFDerivAt
  have hd := (hf.comp T (hasFDerivAt_prodMk_right Y T)).hasDerivAt
  exact hd.unique (stationaryQ_second_hasDerivAt Y T)
lemma stationaryQ_partial_isInvertible (Y : ℝ) (hY : Y ∈ stationaryParameterDomain) :
    (fderiv ℂ stationaryQProd ((Y : ℂ),(WP.T Y : ℂ)) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  apply complex_clm_isInvertible_of_apply_one_ne_zero
  rw [stationaryQ_partial_one]
  have hs := T_root_on_stationaryParameterDomain Y hY
  have hYT : Y < WP.T Y := lt_trans hY.1 hs.1.1
  have hneg := K_deriv_re_neg_before Y (2*(WP.T Y-Y)) (by linarith) (by linarith [hs.1.2])
  have hne : deriv (K Y) ((2*(WP.T Y-Y) : ℝ) : ℂ) ≠ 0 := by
    intro he
    rw [he,Complex.zero_re] at hneg
    exact lt_irrefl _ hneg
  have he : 2*((WP.T Y : ℂ)-(Y : ℂ)) = ((2*(WP.T Y-Y) : ℝ) : ℂ) := by push_cast; ring
  rw [he]
  exact mul_ne_zero (by norm_num) hne
lemma T_analyticAt_on_stationaryParameterDomain (Y : ℝ) (hY : Y ∈ stationaryParameterDomain) :
    AnalyticAt ℝ WP.T Y := by
  have hbase := stationaryQ_zero_of_real_zero Y (WP.T Y)
    (T_root_on_stationaryParameterDomain Y hY).2
  apply analyticAt_real_implicit_continuous_branch stationaryQProd WP.T Y
    stationaryQ_contDiff_one.contDiffAt (stationaryQ_partial_isInvertible Y hY)
    (T_continuousAt_on_stationaryParameterDomain Y hY)
  filter_upwards [stationaryParameterDomain_isOpen.mem_nhds hY] with x hx
  rw [hbase,stationaryQ_zero_of_real_zero x (WP.T x) (T_root_on_stationaryParameterDomain x hx).2]
lemma T_analyticAt_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : AnalyticAt ℝ WP.T Y :=
  T_analyticAt_on_stationaryParameterDomain Y (stationaryParameterDomain_contains Y hY)


end WP.Analysis
