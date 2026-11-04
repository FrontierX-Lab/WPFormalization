import WPFormalization.Analysis.StationaryIntegral
import WPFormalization.Analysis.FirstKernelRoot

/-! Identification of the original stationary infimum with the actual first K root.
The candidate Y+r(Y)/2 lies above y₀ because the kernel integral remains
positive while all its arguments lie before the first derivative zero. Every
stationary zero gives a positive K zero through the proved Abel transform;
the minimal-root property identifies the infimum. The physical-interval
strict decrease of K gives the stated uniqueness and the π²/4 upper bound.
-/
noncomputable section
namespace WP
open Set
lemma K_re_pos_before_critical (Y z : ℝ) (hY : Y ∈ Ico 0 y₀) (hz : 0 ≤ z)
    (ht : Y+z/2 ≤ y₀) : 0 < (K Y z).re := by
  rw [K_real_integral]
  apply intervalIntegral.integral_pos zero_lt_one
  · apply Continuous.continuousOn
    exact Analysis.a_continuous.comp (by fun_prop)
  · intro s hs
    have harg0 : 0 ≤ Y+z/2*(1-s^2) := by
      have he : 0 ≤ 1-s^2 := by nlinarith [hs.1,hs.2]
      exact add_nonneg hY.1 (mul_nonneg (div_nonneg hz (by norm_num)) he)
    have harg : Y+z/2*(1-s^2) ≤ y₀ := by
      nlinarith [mul_nonneg hz (sq_nonneg s)]
    by_cases he : Y+z/2*(1-s^2) = y₀
    · rw [he,a_y₀_zero]
    · exact (a_pos _ ⟨harg0,lt_of_le_of_ne harg he⟩).le
  · refine ⟨1,⟨zero_le_one,le_rfl⟩,?_⟩
    simpa using a_pos Y hY

lemma firstKernelEndpoint_gt (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    y₀ < Y+r Y/2 := by
  by_contra h
  have ht : Y+r Y/2 ≤ y₀ := le_of_not_gt h
  have hp := K_re_pos_before_critical Y (r Y) hY (r_pos Y hY).le ht
  rw [Analysis.K_r_zero Y hY,Complex.zero_re] at hp
  exact lt_irrefl _ hp

lemma firstKernelEndpoint_stationary (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    (∫ v in Y..(Y+r Y/2),a v/Real.sqrt ((Y+r Y/2)-v)) = 0 := by
  have hYT : Y < Y+r Y/2 := by linarith [r_pos Y hY]
  rw [stationary_integral_kernel Y (Y+r Y/2) hYT]
  have he : (2*((Y+r Y/2)-Y) : ℝ) = r Y := by ring
  rw [he,Analysis.K_r_zero Y hY,Complex.zero_re,mul_zero]

lemma stationary_sInf_eq_firstKernelEndpoint (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    sInf {t : ℝ | y₀ < t ∧ (∫ v in Y..t,a v/Real.sqrt (t-v)) = 0} = Y+r Y/2 := by
  let S := {t : ℝ | y₀ < t ∧ (∫ v in Y..t,a v/Real.sqrt (t-v)) = 0}
  have hmem : Y+r Y/2 ∈ S := ⟨firstKernelEndpoint_gt Y hY,firstKernelEndpoint_stationary Y hY⟩
  have hlower : ∀ t ∈ S,Y+r Y/2 ≤ t := by
    intro t ht
    have hYt : Y < t := lt_trans hY.2 ht.1
    have he := ht.2
    rw [stationary_integral_kernel Y t hYt] at he
    have hpos : 0 < 2*Real.sqrt (t-Y) := by positivity
    have hre : (K Y ((2*(t-Y) : ℝ) : ℂ)).re = 0 :=
      (mul_eq_zero.mp he).resolve_left (ne_of_gt hpos)
    have hroot : K Y ((2*(t-Y) : ℝ) : ℂ) = 0 := by
      apply Complex.ext
      · simpa using hre
      · change (Analysis.rootKernel (Y : ℂ) ((2*(t-Y) : ℝ) : ℂ)).im = 0
        exact Analysis.rootKernel_real Y (2*(t-Y))
    have hr := Analysis.r_le_of_K_zero Y (2*(t-Y)) (by linarith) hroot
    linarith
  have hB : BddBelow S := ⟨Y+r Y/2,hlower⟩
  exact le_antisymm (csInf_le hB hmem) (le_csInf ⟨_,hmem⟩ hlower)

lemma stationary_zero_iff_K_zero (Y T : ℝ) (hYT : Y < T) :
    (∫ v in Y..T,a v/Real.sqrt (T-v)) = 0 ↔
      K Y ((2*(T-Y) : ℝ) : ℂ) = 0 := by
  rw [stationary_integral_kernel Y T hYT]
  constructor
  · intro he
    have hpos : 0 < 2*Real.sqrt (T-Y) := by positivity
    have hre := (mul_eq_zero.mp he).resolve_left (ne_of_gt hpos)
    apply Complex.ext
    · simpa using hre
    · change (Analysis.rootKernel (Y : ℂ) ((2*(T-Y) : ℝ) : ℂ)).im = 0
      exact Analysis.rootKernel_real Y (2*(T-Y))
  · intro he
    rw [he,Complex.zero_re,mul_zero]

lemma stationary_firstKernelEndpoint_unique (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    Y+r Y/2 ∈ Ioc y₀ (Real.pi^2/4) ∧
    (∫ v in Y..(Y+r Y/2),a v/Real.sqrt ((Y+r Y/2)-v)) = 0 ∧
    ∀ t ∈ Ioc y₀ (Real.pi^2/4), (∫ v in Y..t,a v/Real.sqrt (t-v)) = 0 → t = Y+r Y/2 := by
  refine ⟨⟨firstKernelEndpoint_gt Y hY,?_⟩,firstKernelEndpoint_stationary Y hY,?_⟩
  · linarith [Analysis.r_le_pi Y hY]
  · intro t ht hzero
    have hYt : Y < t := lt_trans hY.2 ht.1
    have hroot := (stationary_zero_iff_K_zero Y t hYt).mp hzero
    have he := Analysis.K_zero_unique_interval Y (2*(t-Y)) hY
      ⟨by linarith,by linarith [ht.2]⟩ hroot
    linarith
end WP
