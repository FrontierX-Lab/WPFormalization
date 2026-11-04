import WPFormalization.Analysis.StationaryAnalytic
import WPFormalization.Analysis.ParameterIdentities

/-! A genuine local analytic stationary germ at the critical point.
The original sInf-defined T agrees with this germ only from the left; no
identification with the right-hand original root is asserted. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology ContDiff
lemma real_clm_isInvertible_of_apply_one_ne_zero (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) :
    L.IsInvertible := by
  have he (z : ℝ) : L z = (L 1)*z := by
    simpa only [smul_eq_mul,mul_one,mul_comm] using L.map_smul z (1 : ℝ)
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · apply ContinuousLinearMap.ext
    intro z
    change L ((L 1)⁻¹*z) = z
    rw [he ((L 1)⁻¹*z)]
    field_simp [h]
  · apply ContinuousLinearMap.ext
    intro z
    change (L 1)⁻¹*L z = z
    rw [he z]
    field_simp [h]
def stationaryQRealProd (p : ℝ × ℝ) : ℝ := stationaryQReal p.1 p.2
lemma stationaryQRealProd_contDiff_one : ContDiff ℝ 1 stationaryQRealProd := by
  have hC : ContDiff ℝ 1 stationaryQProd := stationaryQ_contDiff_one.restrict_scalars ℝ
  have hp : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((p.1:ℂ),(p.2:ℂ))) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst).prodMk (Complex.ofRealCLM.contDiff.comp contDiff_snd)
  exact Complex.reCLM.contDiff.comp (hC.comp hp)
lemma stationaryQRealProd_second_one (Y T : ℝ) :
    (fderiv ℝ stationaryQRealProd (Y,T) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) 1 =
      (2*deriv (K Y) (2*((T:ℂ)-(Y:ℂ)))).re := by
  have hf := (stationaryQRealProd_contDiff_one.differentiable (by norm_num) (Y,T)).hasFDerivAt
  have hd := (hf.comp T (hasFDerivAt_prodMk_right Y T)).hasDerivAt
  exact hd.unique (stationaryQ_second_hasDerivAt (Y:ℂ) (T:ℂ)).real_of_complex
lemma stationaryQRealProd_critical_partial_isInvertible :
    (fderiv ℝ stationaryQRealProd (y₀,y₀) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
  apply real_clm_isInvertible_of_apply_one_ne_zero
  rw [stationaryQRealProd_second_one]
  have hp : y₀ ≤ (5/2:ℝ) := by linarith [y₀_lt_three_halves]
  have hn := K_deriv_re_neg_before y₀ 0 le_rfl (by simpa using hp)
  have hneg := mul_neg_of_pos_of_neg (by norm_num : (0:ℝ) < 2) hn
  apply ne_of_lt
  simpa [Complex.mul_re] using hneg

lemma stationaryQ_critical_partial_isInvertible :
    (fderiv ℂ stationaryQProd ((y₀:ℂ),(y₀:ℂ)) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  apply complex_clm_isInvertible_of_apply_one_ne_zero
  rw [stationaryQ_partial_one]
  have hp : y₀ ≤ (5/2:ℝ) := by linarith [y₀_lt_three_halves]
  have hn := K_deriv_re_neg_before y₀ 0 le_rfl (by simpa using hp)
  have hne : deriv (K y₀) 0 ≠ 0 := by
    intro he
    rw [Complex.ofReal_zero,he,Complex.zero_re] at hn
    exact lt_irrefl _ hn
  simp only [sub_self,mul_zero]
  exact mul_ne_zero (by norm_num) hne
/-- A local real analytic germ at the critical point; this is not the original
sInf branch for Y above y₀. Its equality with the actual T is only claimed on
the left. -/
def criticalStationaryBranch : ℝ → ℝ :=
  stationaryQRealProd_contDiff_one.contDiffAt.implicitFunction (by norm_num : (1:ℕ∞ω) ≠ 0)
    stationaryQRealProd_critical_partial_isInvertible
lemma criticalStationaryBranch_value : criticalStationaryBranch y₀ = y₀ :=
  stationaryQRealProd_contDiff_one.contDiffAt.implicitFunction_apply_self _ _
lemma criticalStationaryBranch_contDiffAt : ContDiffAt ℝ 1 criticalStationaryBranch y₀ :=
  stationaryQRealProd_contDiff_one.contDiffAt.contDiffAt_implicitFunction _ _
lemma stationaryQRealProd_critical_zero : stationaryQRealProd (y₀,y₀) = 0 := by
  change (stationaryQProd ((y₀:ℂ),(y₀:ℂ))).re = 0
  rw [stationaryQ_eq_K]
  simp only [sub_self,mul_zero,K_zero,derivX_y₀_zero,Complex.zero_re]
lemma criticalStationaryBranch_root :
    ∀ᶠ Y in 𝓝 y₀,stationaryQReal Y (criticalStationaryBranch Y) = 0 := by
  have he := stationaryQRealProd_contDiff_one.contDiffAt.eventually_apply_implicitFunction
    (by norm_num : (1:ℕ∞ω) ≠ 0) stationaryQRealProd_critical_partial_isInvertible
  rw [stationaryQRealProd_critical_zero] at he
  simpa only [stationaryQRealProd,criticalStationaryBranch] using he
lemma criticalStationaryBranch_analyticAt : AnalyticAt ℝ criticalStationaryBranch y₀ := by
  have hV := criticalStationaryBranch_value
  have hInv : (fderiv ℂ stationaryQProd ((y₀:ℂ),(criticalStationaryBranch y₀:ℂ)) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    simpa only [hV] using stationaryQ_critical_partial_isInvertible
  apply analyticAt_real_implicit_continuous_branch stationaryQProd criticalStationaryBranch y₀
    stationaryQ_contDiff_one.contDiffAt hInv criticalStationaryBranch_contDiffAt.continuousAt
  have hbase := stationaryQ_zero_of_real_zero y₀ y₀ stationaryQRealProd_critical_zero
  filter_upwards [criticalStationaryBranch_root] with Y hY
  rw [hV,hbase,stationaryQ_zero_of_real_zero Y _ hY]
lemma T_eventually_eq_criticalStationaryBranch :
    WP.T =ᶠ[𝓝[<] y₀] criticalStationaryBranch := by
  have he := stationaryQRealProd_contDiff_one.contDiffAt.eventually_apply_eq_iff_implicitFunction
    (by norm_num : (1:ℕ∞ω) ≠ 0) stationaryQRealProd_critical_partial_isInvertible
  have hp : Tendsto (fun Y : ℝ => (Y,WP.T Y)) (𝓝[<] y₀) (𝓝 (y₀,y₀)) := by
    simpa only [← nhds_prod_eq,id_eq] using
      (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk WP.T_tendsto_critical
  have hmem : ∀ᶠ Y in 𝓝[<] y₀,Y ∈ Ico 0 y₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hpos
    exact ⟨hpos.le,hY⟩
  filter_upwards [hp.eventually he,hmem] with Y hY hm
  apply Eq.symm
  apply hY.mp
  rw [stationaryQRealProd_critical_zero]
  exact (T_root_on_stationaryParameterDomain Y (stationaryParameterDomain_contains Y hm)).2

end WP.Analysis
