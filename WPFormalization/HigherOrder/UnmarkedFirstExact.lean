import WPFormalization.HigherOrder.Targets
import WPFormalization.HigherOrder.UnmarkedFirstCorrection
import WPFormalization.HigherOrder.FirstScalarCoefficients

noncomputable section
namespace WP.HigherOrder
open WP Filter
open scoped Topology

/-- The first canonical unmarked coefficient, before evaluating the transport term. -/
theorem unmarked_first_algebra (P : PsiTheory) :
    unmarkedCoefficient P 1 =
      1/2 - transportBeta 0 0 + markedCoefficient P 1 1 0 := by
  simp only [unmarkedCoefficient, canonicalUnmarkedSeries, unmarkedProduct,
    PowerSeries.coeff_one_mul, complexityShift_one, complexityShift_constant,
    binomial_constant, formalCusp_constant, binomial_one,
    PowerSeries.constantCoeff_mk, PowerSeries.coeff_mk, markedCoefficient_zero,
    map_mul, mul_one]
  simp only [formalCusp, PowerSeries.coeff_mk]
  rw [cuspCoefficient_one P 0 0 ⟨le_rfl,y₀_pos.le⟩]
  ring

/- The explicit first coefficient from the introduction. The canonical
Gevrey expansion identifies it uniquely with the registered classical
fixed-cusp first correction; no new asymptotic input is assumed. -/
@[blueprint "thm:intro-absolute"]
theorem unmarked_first_exact (P : PsiTheory) :
    unmarkedCoefficient P 1 = 7/6 - 17/(3*Real.pi^2) := by
  let F : ℕ → ℝ := fun g => volumeModel P g 0 / leadingVolume g 0
  let h : ℕ → ℝ := fun g => complexity g 1
  have hs : Tendsto h atTop atTop := Analysis.complexity_real_tendsto_atTop 1
  obtain ⟨C,B,c,N,hC,hB,hc,herr⟩ := unmarked_volume_gevrey_two_sequence P
  let E : ℝ := C*B^2*4
  have hzero : Tendsto (fun g => E/h g) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hs).const_mul E
  have hcanonical : Tendsto (fun g => h g*(F g-1)) atTop
      (𝓝 (unmarkedCoefficient P 1)) := by
    apply real_tendsto_of_abs_error _ _ _ hzero
    filter_upwards [eventually_ge_atTop N,
      hs.eventually (eventually_ge_atTop ((1/c)^2))] with g hg hlarge
    have hd := herr g hg
    have hh : 0 < h g := hd.1
    have hsq : 1 ≤ c^2*h g := by
      have ht := mul_le_mul_of_nonneg_left hlarge (sq_nonneg c)
      have he : c^2*(1/c)^2 = 1 := by field_simp
      rwa [he] at ht
    have hw : (1 : ℝ) ≤ c*Real.sqrt (h g) := by
      have ht := Real.sq_sqrt hh.le
      have hn := mul_nonneg hc.le (Real.sqrt_nonneg (h g))
      nlinarith
    have he := hd.2 1 (by simpa [h] using hw)
    change |F g - Analysis.inversePowerTruncation (canonicalUnmarkedSeries P) 1 (h g)| ≤ _ at he
    have hz : PowerSeries.coeff 0 (canonicalUnmarkedSeries P) = 1 :=
      unmarkedCoefficient_zero P
    simp only [Analysis.inversePowerTruncation, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, pow_zero, div_one, hz, pow_one,
      show PowerSeries.coeff 1 (canonicalUnmarkedSeries P) = unmarkedCoefficient P 1 from rfl] at he
    norm_num only [Nat.add_one_sub_one, Nat.reduceAdd, Nat.factorial_succ,
      Nat.factorial_zero, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, mul_one] at he
    have hm := mul_le_mul_of_nonneg_left he hh.le
    have ha : |h g*(F g-1)-unmarkedCoefficient P 1| =
        h g * |F g-(1+unmarkedCoefficient P 1/h g)| := by
      calc
        _ = |h g*(F g-(1+unmarkedCoefficient P 1/h g))| := by
          congr 1
          field_simp [hh.ne']
          ring
        _ = _ := by rw [abs_mul, abs_of_pos hh]
    rw [ha]
    calc
      _ ≤ h g * (E / (h g)^2) := by simpa [E,h] using hm
      _ = E / h g := by field_simp [hh.ne']
  have hscale : Tendsto (fun g : ℕ => h g/(g : ℝ)) atTop (𝓝 (2 : ℝ)) := by
    have ht := inverse_genus_tendsto_zero.const_sub 2
    simp only [sub_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 2] with g hg
    have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
    have hh : h g = 2*(g : ℝ)-1 := by
      dsimp [h,complexity]
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hh]
    field_simp
  have hclassical := hscale.mul (unmarked_first_correction_limit P)
  have hsecond : Tendsto (fun g => h g*(F g-1)) atTop
      (𝓝 (2*(7/12-17/(6*Real.pi^2)))) := by
    apply hclassical.congr'
    filter_upwards [eventually_ge_atTop 2] with g hg
    have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
    dsimp [F]
    field_simp
  have he := tendsto_nhds_unique hcanonical hsecond
  rw [he]
  ring

end WP.HigherOrder
