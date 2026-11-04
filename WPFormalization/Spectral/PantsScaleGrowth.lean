import WPFormalization.Spectral.ManyEigenvaluesTransfer
import WPFormalization.Analysis.VolumeProfileRegular
import WPFormalization.Analysis.ChainParameterProfile

/-! Growth of the actual geometric pants scale. The cusp count is not
restricted by an upper bound in terms of genus. -/
noncomputable section
namespace WP.Spectral
open Filter Set WP.Analysis
open scoped Topology

lemma profileC_linear_upper (l : ℝ) (hl : 0 ≤ l) :
    profileC l ≤ 4 * Real.pi ^ 2 * (1 + l) := by
  have hs := Analysis.densityY_spec l hl
  have hD := J_sub_XR_pos_interior _ hs.1
  have hx := XR_nonneg_interior _ hs.1
  have hJ : (1 / 2 : ℝ) ≤ J (densityY l) := by
    simpa only [J_zero_value] using
      Analysis.chain_J_strictMonoOn.monotoneOn
        (show (0 : ℝ) ∈ Ico 0 y₀ from ⟨le_rfl, y₀_pos⟩) hs.1 hs.1.1
  have he := density_J_formula_on_domain (densityY l)
    (stationaryParameterDomain_contains _ hs.1)
  rw [hs.2] at he
  have hm : l * (J (densityY l) - XR (densityY l)) = 2 * XR (densityY l) :=
    (eq_div_iff hD.ne').mp he
  have hid : (1 + l) * (J (densityY l) - XR (densityY l)) =
      J (densityY l) + XR (densityY l) := by nlinarith [hm]
  rw [Analysis.volume_profile_C_physical l hl, Analysis.volumeProfileCPhysical]
  apply (div_le_iff₀ hD).2
  rw [mul_assoc (4 * Real.pi ^ 2), hid]
  nlinarith [mul_nonneg (sq_nonneg Real.pi) (show 0 ≤ J (densityY l) + XR (densityY l) - 1 / 2 by linarith)]

lemma pantsScale_lower (g n : ℕ) (hg : 1 ≤ g) (hn : 2 ≤ n) :
    (n : ℝ) ^ 2 / (64 * Real.pi ^ 2 * ((g : ℝ) + n)) ≤ pantsScale g n := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hC := Analysis.volume_profile_C_pos ((n : ℝ) / g) (by positivity)
  have hbound := profileC_linear_upper ((n : ℝ) / g) (by positivity)
  have hden : 8 * (g : ℝ) * profileC ((n : ℝ) / g) ≤
      32 * Real.pi ^ 2 * ((g : ℝ) + n) := by
    have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 8 * (g : ℝ) by positivity)
    have hid : 8 * (g : ℝ) * (4 * Real.pi ^ 2 * (1 + (n : ℝ) / g)) =
        32 * Real.pi ^ 2 * ((g : ℝ) + n) := by field_simp; ring
    exact hh.trans_eq hid
  unfold pantsScale
  apply (div_le_div_iff₀ (by positivity : 0 < 64 * Real.pi ^ 2 * ((g : ℝ) + n))
    (by positivity : 0 < 8 * (g : ℝ) * profileC ((n : ℝ) / g))).2
  have hnum : (n : ℝ) ^ 2 ≤ 2 * ((n : ℝ) * (n - 1)) := by nlinarith
  calc
    (n : ℝ) ^ 2 * (8 * g * profileC ((n : ℝ) / g)) ≤
        (n : ℝ) ^ 2 * (32 * Real.pi ^ 2 * ((g : ℝ) + n)) :=
      mul_le_mul_of_nonneg_left hden (sq_nonneg _)
    _ ≤ (n : ℝ) * (n - 1) * (64 * Real.pi ^ 2 * ((g : ℝ) + n)) := by
      nlinarith [mul_le_mul_of_nonneg_right hnum
        (show 0 ≤ 32 * Real.pi ^ 2 * ((g : ℝ) + n) by positivity)]

theorem pantsScale_tendsto_atTop (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop) :
    Tendsto (fun g => pantsScale g (n g)) atTop atTop := by
  have hn2 := fast_cusps_eventually_two n hn
  have hnreal : Tendsto (fun g => (n g : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hn
    filter_upwards [eventually_ge_atTop 1] with g hg
    have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
    have hs : 1 ≤ Real.sqrt (g : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
    exact div_le_self (by positivity) hs
  have hinv : Tendsto (fun g => (n g : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnreal
  have hsmall : Tendsto (fun g : ℕ => Real.sqrt (g : ℝ) / n g) atTop (𝓝 0) := by
    simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp hn
  let d : ℕ → ℝ := fun g => (Real.sqrt (g : ℝ) / n g) ^ 2 + (n g : ℝ)⁻¹
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [d, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using (hsmall.pow 2).add hinv
  have hdp : ∀ᶠ g in atTop, d g ∈ Ioi 0 := by
    filter_upwards [hn2] with g hg
    have hnpos : (0 : ℝ) < n g := by exact_mod_cast (show 0 < n g by omega)
    dsimp [d]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (inv_pos.mpr hnpos)
  have htop : Tendsto (fun g => (d g)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hd, hdp⟩)
  have hfrac : Tendsto (fun g => (n g : ℝ) ^ 2 / ((g : ℝ) + n g)) atTop atTop := by
    apply htop.congr'
    filter_upwards [hn2] with g hg
    have hne : (n g : ℝ) ≠ 0 := by exact_mod_cast (show n g ≠ 0 by omega)
    have he : d g = ((g : ℝ) + n g) / (n g : ℝ) ^ 2 := by
      dsimp [d]
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg g)]
      field_simp
    rw [he, inv_div]
  have hscaled : Tendsto (fun g => (64 * Real.pi ^ 2)⁻¹ *
      ((n g : ℝ) ^ 2 / ((g : ℝ) + n g))) atTop atTop :=
    hfrac.const_mul_atTop (by positivity)
  apply tendsto_atTop_mono' atTop _ hscaled
  filter_upwards [eventually_ge_atTop 1, hn2] with g hg hng
  convert pantsScale_lower g (n g) hg hng using 1 <;>
    simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

end WP.Spectral
