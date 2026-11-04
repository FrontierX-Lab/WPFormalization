import WPFormalization.Analysis.VolumeProfileRegular

/-! The effective density at a fixed number of geodesic boundaries differs
uniformly from n/g, including at unbounded cusp density. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set

lemma boundary_density_relative_shift (p g n : ℕ) (hg : p + 2 ≤ g) (hn : p ≤ n) :
    |2 * ((n : ℝ) - p) / (2 * g - 2 + p) - (n : ℝ) / g| /
      (1 + min (2 * ((n : ℝ) - p) / (2 * g - 2 + p)) ((n : ℝ) / g)) ≤
        (2 * ((p : ℝ) + 2) ^ 2) / g := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hgR : (p : ℝ) + 2 ≤ g := by exact_mod_cast hg
  have hnR : (p : ℝ) ≤ n := by exact_mod_cast hn
  have hgp : (0 : ℝ) < g := by linarith
  let d : ℝ := 2 * g - 2 + p
  let l : ℝ := 2 * ((n : ℝ) - p) / d
  let m : ℝ := (n : ℝ) / g
  have hgd : (g : ℝ) ≤ d := by dsimp [d]; linarith
  have hd : 0 < d := hgp.trans_le hgd
  have hdg : d ≤ ((p : ℝ) + 2) * g := by
    dsimp [d]
    nlinarith [mul_nonneg hp (show 0 ≤ (g : ℝ) - 1 by linarith)]
  have hl : 0 ≤ l := by dsimp [l]; positivity
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hlg : l * d = 2 * ((n : ℝ) - p) := by dsimp [l]; field_simp
  have hmg : m * g = (n : ℝ) := by dsimp [m]; field_simp
  have hratio : 1 + m ≤ ((p : ℝ) + 2) * (1 + l) := by
    have hh := mul_le_mul_of_nonneg_right hdg hl
    have hbound : m ≤ ((p : ℝ) + 2) * l + 1 := by
      apply (mul_le_mul_iff_right₀ hgp).mp
      nlinarith [hlg, hmg]
    nlinarith
  have hmin : 1 + m ≤ ((p : ℝ) + 2) * (1 + min l m) := by
    rcases le_total l m with h | h
    · simpa only [min_eq_left h] using hratio
    · rw [min_eq_right h]
      nlinarith [mul_nonneg (show 0 ≤ (p : ℝ) + 1 by positivity)
        (show 0 ≤ 1 + m by positivity)]
  have he : (l - m) * d = (2 - (p : ℝ)) * m - 2 * p := by
    dsimp only [d] at hlg ⊢
    nlinarith [hlg, hmg]
  have habs : |2 - (p : ℝ)| ≤ (p : ℝ) + 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hcore : |l - m| * g ≤ 2 * ((p : ℝ) + 2) * (1 + m) := by
    calc
      |l - m| * g ≤ |l - m| * d := mul_le_mul_of_nonneg_left hgd (abs_nonneg _)
      _ = |(2 - (p : ℝ)) * m - 2 * p| := by rw [← abs_of_pos hd, ← abs_mul, he]
      _ ≤ |(2 - (p : ℝ)) * m| + |2 * (p : ℝ)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le ((2 - (p : ℝ)) * m) 0 (2 * (p : ℝ))
      _ ≤ ((p : ℝ) + 2) * m + 2 * p := by
        rw [abs_mul, abs_of_nonneg hm, abs_of_nonneg (by positivity : 0 ≤ 2 * (p : ℝ))]
        exact add_le_add (mul_le_mul_of_nonneg_right habs hm) le_rfl
      _ ≤ 2 * ((p : ℝ) + 2) * (1 + m) := by nlinarith
  have hminpos : 0 < 1 + min l m := by positivity
  change |l - m| / (1 + min l m) ≤ (2 * ((p : ℝ) + 2) ^ 2) / g
  apply (div_le_div_iff₀ hminpos hgp).2
  have hh := mul_le_mul_of_nonneg_left hmin (show 0 ≤ 2 * ((p : ℝ) + 2) by positivity)
  nlinarith

lemma boundary_densityY_shift (p g n : ℕ) (hg : p + 2 ≤ g) (hn : p ≤ n) :
    |densityY (2 * ((n : ℝ) - p) / (2 * g - 2 + p)) - densityY ((n : ℝ) / g)| ≤
      (Real.pi ^ 2 * ((p : ℝ) + 2) ^ 2) / g := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hgR : (p : ℝ) + 2 ≤ g := by exact_mod_cast hg
  have hnR : (p : ℝ) ≤ n := by exact_mod_cast hn
  have hgp : (0 : ℝ) < g := by linarith
  have hden : (0 : ℝ) < 2 * g - 2 + p := by linarith
  have hh := Analysis.volume_profile_densityY_weighted_difference
    (2 * ((n : ℝ) - p) / (2 * g - 2 + p)) ((n : ℝ) / g)
    (by positivity) (by positivity)
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_left (boundary_density_relative_shift p g n hg hn)
    (show 0 ≤ Real.pi ^ 2 / 2 by positivity)
  convert hb using 1 <;> ring

end WP.BoundaryConvolution
