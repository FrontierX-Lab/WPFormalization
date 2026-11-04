import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Exact real-power constants for the critical action in edge coordinates.
These algebraic identities require only positive real scalars. -/
noncomputable section
namespace WP.Analysis

lemma jt_critical_delta_constant (b : ℝ) :
    (2 / 15 : ℝ) * b * (3 : ℝ) ^ (3 / 2 : ℝ) =
      2 * Real.sqrt 3 * b / 5 := by
  have hthree : (3 : ℝ) ^ (3 / 2 : ℝ) = 3 * Real.sqrt 3 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [hthree]
  ring

lemma jt_critical_gap_constant (b : ℝ) (hb : 0 < b) :
    ((2 / 15 : ℝ) * b * (3 : ℝ) ^ (3 / 2 : ℝ)) /
        (b / 2) ^ (5 / 4 : ℝ) =
      (2 : ℝ) ^ (9 / 4 : ℝ) * Real.sqrt 3 /
        (5 * b ^ (1 / 4 : ℝ)) := by
  have hbpow : b ^ (5 / 4 : ℝ) = b * b ^ (1 / 4 : ℝ) := by
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num,
      Real.rpow_add hb, Real.rpow_one]
  have htwo : (2 : ℝ) ^ (9 / 4 : ℝ) = 2 * (2 : ℝ) ^ (5 / 4 : ℝ) := by
    rw [show (9 / 4 : ℝ) = 1 + 5 / 4 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  rw [jt_critical_delta_constant,
    Real.div_rpow hb.le (by norm_num : (0 : ℝ) ≤ 2), hbpow, htwo]
  have hbp := (Real.rpow_pos_of_pos hb (1 / 4 : ℝ)).ne'
  have htp := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (5 / 4 : ℝ)).ne'
  field_simp [hb.ne', hbp, htp]

lemma jt_gap_power_factor (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B) :
    (δ ^ 2 * B) ^ (5 / 4 : ℝ) =
      δ ^ (5 / 2 : ℝ) * B ^ (5 / 4 : ℝ) := by
  rw [Real.mul_rpow (sq_nonneg δ) hB,
    ← Real.rpow_natCast_mul hδ 2 (5 / 4 : ℝ)]
  norm_num

end WP.Analysis
