import WPFormalization.Analysis.KernelZeroValues
import WPFormalization.Statements.Parameter

/-! The ordinary WP instanton action and its exact saddle dictionary. These
are identities of the paper's actual entire kernel, with no physical-volume
prediction as a premise. -/
noncomputable section
namespace WP.Analysis
open Set

def instantonAction (w : ℂ) : ℂ :=
  (Complex.sin (2 * Real.pi * w) -
    2 * Real.pi * w * Complex.cos (2 * Real.pi * w)) / (4 * (Real.pi : ℂ)^3)

theorem instantonAction_entire : Differentiable ℂ instantonAction := by
  unfold instantonAction
  fun_prop

theorem instantonAction_eq_H (w : ℂ) :
    instantonAction w = (2/3 : ℂ) * w^3 * H 0 (2 * (Real.pi : ℂ)^2 * w^2) := by
  have hs := rootKernel_sine (2 * (Real.pi : ℂ) * w)
  have hd := K_zero_sine_derivative (2 * (Real.pi : ℂ) * w)
  have hz : (2 * (Real.pi : ℂ) * w)^2 / 2 = 2 * (Real.pi : ℂ)^2 * w^2 := by ring
  rw [hz] at hs hd
  change 2 * (Real.pi : ℂ) * w * K 0 (2 * (Real.pi : ℂ)^2 * w^2) =
    Complex.sin (2 * (Real.pi : ℂ) * w) at hs
  rw [H_zero_eq_K_deriv]
  unfold instantonAction
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero _ hp))).2
  linear_combination (2 * (Real.pi : ℂ) * w) * hd - hs

theorem instantonAction_hasDerivAt (w : ℂ) :
    HasDerivAt instantonAction (w * Complex.sin (2 * Real.pi * w) / Real.pi) w := by
  have harg : HasDerivAt (fun z : ℂ => 2 * Real.pi * z) (2 * Real.pi) w :=
    by simpa using (hasDerivAt_id w).const_mul (2 * (Real.pi : ℂ))
  have hd := ((Complex.hasDerivAt_sin (2 * Real.pi * w)).comp w harg).sub
    (harg.mul ((Complex.hasDerivAt_cos (2 * Real.pi * w)).comp w harg))
  convert hd.div_const (4 * (Real.pi : ℂ)^3) using 1
  · rfl
  · have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    dsimp only [Function.comp_apply]
    field_simp
    ring

theorem instantonAction_log_derivative (w : ℂ) (_hw : instantonAction w ≠ 0) :
    w * deriv instantonAction w / instantonAction w =
      (2 * Real.pi * w)^2 * Complex.sin (2 * Real.pi * w) /
        (Complex.sin (2 * Real.pi * w) -
          2 * Real.pi * w * Complex.cos (2 * Real.pi * w)) := by
  rw [(instantonAction_hasDerivAt w).deriv]
  unfold instantonAction
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

def instantonActionReal (w : ℝ) : ℝ :=
  (Real.sin (2 * Real.pi * w) -
    2 * Real.pi * w * Real.cos (2 * Real.pi * w)) / (4 * Real.pi^3)

theorem instantonAction_ofReal (w : ℝ) :
    instantonAction (w : ℂ) = (instantonActionReal w : ℂ) := by
  simp only [instantonAction, instantonActionReal, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.ofReal_sin, Complex.ofReal_cos]

theorem instantonActionReal_hasDerivAt (w : ℝ) :
    HasDerivAt instantonActionReal (w * Real.sin (2 * Real.pi * w) / Real.pi) w := by
  have harg : HasDerivAt (fun z : ℝ => 2 * Real.pi * z) (2 * Real.pi) w :=
    by simpa using (hasDerivAt_id w).const_mul (2 * Real.pi)
  have hd := ((Real.hasDerivAt_sin (2 * Real.pi * w)).comp w harg).sub
    (harg.mul ((Real.hasDerivAt_cos (2 * Real.pi * w)).comp w harg))
  convert hd.div_const (4 * Real.pi^3) using 1
  · rfl
  · dsimp only [Function.comp_apply]
    field_simp
    ring

theorem instantonActionReal_pos (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
    0 < instantonActionReal (t / (2 * Real.pi)) := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have he : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
  simp only [instantonActionReal, he]
  exact div_pos (trigDen_pos t ⟨ht.1, ht.2.le⟩) (by positivity)

theorem instantonActionReal_log_derivative (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
    (t / (2 * Real.pi)) * deriv instantonActionReal (t / (2 * Real.pi)) /
      instantonActionReal (t / (2 * Real.pi)) = densityTrig t := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hd : trigDen t ≠ 0 := (trigDen_pos t ⟨ht.1, ht.2.le⟩).ne'
  have he : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
  rw [(instantonActionReal_hasDerivAt _).deriv]
  simp only [instantonActionReal, he, densityTrig, trigDen] at *
  field_simp
  ring

/-- The logarithm of the factor multiplying `dw/w`; the exponent is `2k+1`. -/
def instantonSaddleExponent (g k : ℕ) (w : ℝ) : ℝ :=
  (2 * (k : ℝ) + 1) * Real.log w - (2 * (g : ℝ) - 1) * Real.log (instantonActionReal w)

theorem instantonSaddleExponent_hasDerivAt (g k : ℕ) (w : ℝ)
    (hw : w ≠ 0) (hA : instantonActionReal w ≠ 0) :
    HasDerivAt (instantonSaddleExponent g k)
      ((2 * (k : ℝ) + 1) / w - (2 * (g : ℝ) - 1) *
        deriv instantonActionReal w / instantonActionReal w) w := by
  convert ((Real.hasDerivAt_log hw).const_mul (2 * (k : ℝ) + 1)).sub
    (((instantonActionReal_hasDerivAt w).log hA).const_mul (2 * (g : ℝ) - 1)) using 1
  · rfl
  · rw [(instantonActionReal_hasDerivAt w).deriv]
    ring

theorem instanton_stationary_iff_trig (g k : ℕ) (hg : 1 ≤ g)
    (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
    deriv (instantonSaddleExponent g k) (t / (2 * Real.pi)) = 0 ↔
      densityTrig t = (2 * (k : ℝ) + 1) / (2 * (g : ℝ) - 1) := by
  have hw : t / (2 * Real.pi) ≠ 0 := (div_pos ht.1 (by positivity)).ne'
  have hA := (instantonActionReal_pos t ht).ne'
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hh : 2 * (g : ℝ) - 1 ≠ 0 := by linarith
  rw [(instantonSaddleExponent_hasDerivAt g k _ hw hA).deriv,
    ← instantonActionReal_log_derivative t ht]
  have ht0 : t ≠ 0 := ht.1.ne'
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  constructor <;> intro he <;> nlinarith only [he]

theorem instanton_trigSaddle_stationary (g k : ℕ) (hg : 1 ≤ g)
    (hk : k < 3*g-2) :
    deriv (instantonSaddleExponent g k) (trigSaddle g k / (2 * Real.pi)) = 0 := by
  have ht := trig_saddle_spec g k hg hk
  apply (instanton_stationary_iff_trig g k hg _ ht.1).2
  exact ht.2.1

end WP.Analysis
