import Mathlib
/-! The quarter-power central window fits the actual Fourier period under a proved variance lower bound. -/
noncomputable section
namespace WP.Analysis
lemma quarter_fourier_window (h v τ b:ℝ) (hh:1≤h) (hτ:0≤τ) (hτ1:τ≤1)
    (hb:0<b) (hbv:b≤Real.sqrt v) (hτb:τ≤Real.pi*b) :
    (τ*Real.sqrt (Real.sqrt h))^2≤h ∧
      τ*Real.sqrt (Real.sqrt h)≤Real.pi*Real.sqrt (h*v) := by
  have hh0:0<h:=zero_lt_one.trans_le hh
  have hs:0≤Real.sqrt h:=Real.sqrt_nonneg h
  have hs1:1≤Real.sqrt h:=by simpa using Real.sqrt_le_sqrt hh
  have hsH:Real.sqrt h≤h:=(Real.sqrt_le_iff).mpr ⟨hh0.le,by nlinarith⟩
  have hss:Real.sqrt (Real.sqrt h)≤Real.sqrt h:=Real.sqrt_le_sqrt hsH
  have hτsq:τ^2≤1:=pow_le_one₀ hτ hτ1
  constructor
  · rw[mul_pow,Real.sq_sqrt hs]
    exact (mul_le_of_le_one_left hs hτsq).trans hsH
  · rw[Real.sqrt_mul hh0.le]
    calc _ ≤ τ*Real.sqrt h:=mul_le_mul_of_nonneg_left hss hτ
         _ ≤ (Real.pi*b)*Real.sqrt h:=mul_le_mul_of_nonneg_right hτb hs
         _ ≤ (Real.pi*Real.sqrt v)*Real.sqrt h:=mul_le_mul_of_nonneg_right
               (mul_le_mul_of_nonneg_left hbv Real.pi_pos.le) hs
         _ = _:=by ring
end WP.Analysis
