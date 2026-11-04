import WPFormalization.Analysis.ComplexGermGluing
import WPFormalization.Analysis.CriticalKernelLipschitz

/-! A genuine common complex continuation of the actual stationary branch.
At the critical point the proved implicit germ is used; only equality on the
physical closed interval is asserted. The continued root has critical value
zero and derivative -3, with no assertion about totalized r to the right.
The canonical total weight extends by -2 times the stationary derivative. -/
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace WP.Analysis

lemma stationary_local_complex_extension (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    ∃ r : ℝ,0 < r ∧ ∃ ψ : ℂ → ℂ,AnalyticOnNhd ℂ ψ (Metric.ball (Y:ℂ) r) ∧
      ∀ t ∈ Icc (0:ℝ) y₀,(t:ℂ) ∈ Metric.ball (Y:ℂ) r → ψ (t:ℂ)=(T t:ℂ) := by
  have hlocal : ∃ ψ : ℂ → ℂ,AnalyticAt ℂ ψ (Y:ℂ) ∧
      ∀ᶠ t : ℝ in 𝓝 Y,t ∈ Icc (0:ℝ) y₀ → ψ (t:ℂ)=(T t:ℂ) := by
    by_cases hcrit : Y=y₀
    · subst Y
      have hInv : (fderiv ℂ stationaryQProd ((y₀:ℂ),(criticalStationaryBranch y₀:ℂ)) ∘L
          ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
        simpa only [criticalStationaryBranch_value] using stationaryQ_critical_partial_isInvertible
      have hEq : ∀ᶠ t : ℝ in 𝓝 y₀,
          stationaryQProd ((t:ℂ),(criticalStationaryBranch t:ℂ))=
            stationaryQProd ((y₀:ℂ),(criticalStationaryBranch y₀:ℂ)) := by
        have hbase := stationaryQ_zero_of_real_zero y₀ y₀ stationaryQRealProd_critical_zero
        filter_upwards [criticalStationaryBranch_root] with t ht
        rw [criticalStationaryBranch_value,hbase,stationaryQ_zero_of_real_zero t _ ht]
      obtain ⟨ψ,hψ,heψ⟩ := exists_complex_implicit_extension stationaryQProd criticalStationaryBranch y₀
        stationaryQ_contDiff_one.contDiffAt hInv criticalStationaryBranch_contDiffAt.continuousAt hEq
      refine ⟨ψ,hψ,?_⟩
      have heT := T_eventually_eq_criticalStationaryBranch
      rw [Filter.EventuallyEq,eventually_nhdsWithin_iff] at heT
      filter_upwards [heψ,heT] with t htψ htT htc
      by_cases ht : t=y₀
      · subst t
        simpa only [criticalStationaryBranch_value,T,ite_true] using htψ
      · exact htψ.trans (congrArg Complex.ofReal (htT (lt_of_le_of_ne htc.2 ht)).symm)
    · have hYi : Y ∈ Ico (0:ℝ) y₀ := ⟨hY.1,lt_of_le_of_ne hY.2 hcrit⟩
      have hDom := stationaryParameterDomain_contains Y hYi
      have hEq : ∀ᶠ t : ℝ in 𝓝 Y,stationaryQProd ((t:ℂ),(T t:ℂ))=
          stationaryQProd ((Y:ℂ),(T Y:ℂ)) := by
        have hbase := stationaryQ_zero_of_real_zero Y (T Y) (T_root_on_stationaryParameterDomain Y hDom).2
        filter_upwards [stationaryParameterDomain_isOpen.mem_nhds hDom] with t ht
        rw [hbase,stationaryQ_zero_of_real_zero t (T t) (T_root_on_stationaryParameterDomain t ht).2]
      obtain ⟨ψ,hψ,heψ⟩ := exists_complex_implicit_extension stationaryQProd T Y
        stationaryQ_contDiff_one.contDiffAt (stationaryQ_partial_isInvertible Y hDom)
        (T_continuousAt_on_stationaryParameterDomain Y hDom) hEq
      exact ⟨ψ,hψ,heψ.mono (fun t ht _ => ht)⟩
  obtain ⟨ψ,hψ,heψ⟩ := hlocal
  obtain ⟨r,hr,ha,he⟩ := complex_extension_ball_of_real_germ 0 y₀ Y (fun t => (T t:ℂ)) ψ hψ heψ
  exact ⟨r,hr,ψ,ha,he⟩

lemma stationary_common_complex_extension :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ (∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω) ∧
      ∃ F : ℂ → ℂ,AnalyticOnNhd ℂ F Ω ∧ ∀ Y ∈ Icc (0:ℝ) y₀,F (Y:ℂ)=(T Y:ℂ) :=
  exists_common_complex_extension 0 y₀ (fun Y => (T Y:ℂ)) stationary_local_complex_extension

lemma stationary_common_connected_complex_extension :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ IsPreconnected Ω ∧ (∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω) ∧
      ∃ F : ℂ → ℂ,AnalyticOnNhd ℂ F Ω ∧ ∀ Y ∈ Icc (0:ℝ) y₀,F (Y:ℂ)=(T Y:ℂ) := by
  obtain ⟨U,hU,hcover,F,hF,hmatch⟩ := stationary_common_complex_extension
  let S : Set ℂ := Complex.ofReal '' Icc (0:ℝ) y₀
  have hS : IsPreconnected S := isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
  have h0 : (0:ℂ) ∈ S := ⟨0,⟨le_rfl,y₀_pos.le⟩,Complex.ofReal_zero⟩
  have hSU : S ⊆ U := by rintro z ⟨Y,hY,rfl⟩;exact hcover Y hY
  have hSc := hS.subset_connectedComponentIn h0 hSU
  refine ⟨connectedComponentIn U 0,hU.connectedComponentIn,isPreconnected_connectedComponentIn,
    ?_,F,hF.mono (connectedComponentIn_subset U 0),hmatch⟩
  intro Y hY
  exact hSc ⟨Y,hY,rfl⟩

lemma T_eventually_eq_criticalStationaryBranch_closed :
    T =ᶠ[𝓝[Icc (0:ℝ) y₀] y₀] criticalStationaryBranch := by
  have he := T_eventually_eq_criticalStationaryBranch
  rw [Filter.EventuallyEq,eventually_nhdsWithin_iff] at he ⊢
  filter_upwards [he] with t ht htc
  by_cases hc : t=y₀
  · subst t
    simp only [T,ite_true,criticalStationaryBranch_value]
  · exact ht (lt_of_le_of_ne htc.2 hc)

lemma stationary_extension_deriv_interior (Ω : Set ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Ω) (hcover : ∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω)
    (hmatch : ∀ Y ∈ Icc (0:ℝ) y₀,F (Y:ℂ)=(T Y:ℂ))
    (Y : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) : deriv F (Y:ℂ)=((deriv T Y:ℝ):ℂ) := by
  apply complex_deriv_eq_of_real_interval_germ 0 y₀ Y (deriv T Y) F T y₀_pos ⟨hY.1,hY.2.le⟩
    (hF _ (hcover Y ⟨hY.1,hY.2.le⟩)).differentiableAt
    (T_analyticAt_interior Y hY).differentiableAt.hasDerivAt
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hmatch t ht

lemma stationary_extension_deriv_critical (Ω : Set ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Ω) (hcover : ∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω)
    (hmatch : ∀ Y ∈ Icc (0:ℝ) y₀,F (Y:ℂ)=(T Y:ℂ)) :
    deriv F (y₀:ℂ)=(-1/2:ℂ) := by
  have hb : HasDerivAt criticalStationaryBranch (-1/2:ℝ) y₀ := by
    rw [←criticalStationaryBranch_deriv_value]
    exact criticalStationaryBranch_analyticAt.differentiableAt.hasDerivAt
  have he : (fun t : ℝ => F (t:ℂ)) =ᶠ[𝓝[Icc (0:ℝ) y₀] y₀]
      (fun t => (criticalStationaryBranch t:ℂ)) := by
    filter_upwards [self_mem_nhdsWithin,T_eventually_eq_criticalStationaryBranch_closed] with t ht he
    rw [hmatch t ht,he]
  have hd := complex_deriv_eq_of_real_interval_germ 0 y₀ y₀ (-1/2) F criticalStationaryBranch y₀_pos
    ⟨y₀_pos.le,le_rfl⟩ (hF _ (hcover y₀ ⟨y₀_pos.le,le_rfl⟩)).differentiableAt hb he
  simpa only [Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat] using hd

lemma stationary_root_mass_common_complex_extension :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ IsPreconnected Ω ∧ (∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω) ∧
      ∃ F R Q : ℂ → ℂ,AnalyticOnNhd ℂ F Ω ∧ AnalyticOnNhd ℂ R Ω ∧ AnalyticOnNhd ℂ Q Ω ∧
        (∀ Y ∈ Icc (0:ℝ) y₀,F (Y:ℂ)=(T Y:ℂ) ∧ Q (Y:ℂ)=(((∑'l : ℕ,weight Y l):ℝ):ℂ)) ∧
        (∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 := by
  obtain ⟨Ω,hΩ,hconn,hcover,F,hF,hmatch⟩ := stationary_common_connected_complex_extension
  let R : ℂ → ℂ := fun z => 2*(F z-z)
  let Q : ℂ → ℂ := fun z => -2*deriv F z
  have hR : AnalyticOnNhd ℂ R Ω := fun z hz => analyticAt_const.mul ((hF z hz).sub analyticAt_id)
  have hQ : AnalyticOnNhd ℂ Q Ω := fun z hz => analyticAt_const.mul (hF z hz).deriv
  refine ⟨Ω,hΩ,hconn,hcover,F,R,Q,hF,hR,hQ,?_,?_,?_,?_⟩
  · intro Y hY
    refine ⟨hmatch Y hY,?_⟩
    by_cases he : Y=y₀
    · subst Y
      dsimp [Q]
      rw [stationary_extension_deriv_critical Ω F hF hcover hmatch,total_weight_critical_value]
      norm_num
    · have hYi : Y ∈ Ico (0:ℝ) y₀ := ⟨hY.1,lt_of_le_of_ne hY.2 he⟩
      dsimp [Q]
      rw [stationary_extension_deriv_interior Ω F hF hcover hmatch Y hYi,
        Theta_eq_neg_two_T_deriv Y hYi]
      push_cast
      ring
  · intro Y hY
    dsimp [R]
    rw [hmatch Y ⟨hY.1,hY.2.le⟩,T_eq_firstKernelEndpoint Y hY]
    push_cast
    ring
  · dsimp [R]
    rw [hmatch y₀ ⟨y₀_pos.le,le_rfl⟩]
    simp [T]
  · have hd := (((hF (y₀:ℂ) (hcover y₀ ⟨y₀_pos.le,le_rfl⟩)).differentiableAt.hasDerivAt.sub
      (hasDerivAt_id (y₀:ℂ))).const_mul (2:ℂ)).deriv
    rw [stationary_extension_deriv_critical Ω F hF hcover hmatch] at hd
    norm_num only at hd
    simpa only [R,Pi.sub_def,id_eq] using hd

end WP.Analysis
