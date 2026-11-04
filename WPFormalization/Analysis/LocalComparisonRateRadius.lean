import Mathlib
noncomputable section
namespace WP.Analysis

lemma local_comparison_radius_budget (A ρ Kmean : ℝ)
    (hA : 0 < A) (hρ : 0 < ρ) (hKm : 0 < Kmean) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ h k hx : ℝ,
      2 ≤ h → C₀*Real.log h ≤ min h k → k ≤ Kmean*h*hx →
      0 < Real.sqrt (A*Real.log h) ∧
      (Real.sqrt (A*Real.log h))^2=A*Real.log h ∧
      (Real.sqrt (A*Real.log h))^2 ≤ h ∧
      Real.sqrt (A*Real.log h) ≤ h ∧
      16*Real.sqrt (A*Real.log h) < ρ*Real.sqrt h ∧
      16*Real.sqrt (A*Real.log h) < ρ*Real.sqrt (h*hx) := by
  let C₀ : ℝ := 1+A+256*A*(1+Kmean)/ρ^2
  have hρsq : 0 < ρ^2 := sq_pos_of_pos hρ
  have hC : 0 < C₀ := by dsimp [C₀]; positivity
  have hCA : A ≤ C₀ := by
    have hz : 0 ≤ 256*A*(1+Kmean)/ρ^2 := by positivity
    dsimp [C₀]
    linarith
  have hCexact : ρ^2*C₀ = ρ^2*(1+A)+256*A*(1+Kmean) := by
    dsimp [C₀]
    field_simp
    <;> ring
  have hcompact : 256*A < ρ^2*C₀ := by
    rw [hCexact]
    nlinarith [mul_pos hA hKm,mul_pos hρsq (show 0 < 1+A by linarith)]
  have horigin : 256*A*Kmean < ρ^2*C₀ := by
    rw [hCexact]
    nlinarith [mul_pos hρsq (show 0 < 1+A by linarith)]
  refine ⟨C₀,hC,?_⟩
  intro h k hx hh hw hk
  have hh0 : 0 < h := by linarith
  have hlog : 0 < Real.log h := Real.log_pos (by linarith)
  have hAl : 0 < A*Real.log h := mul_pos hA hlog
  have hT : 0 < Real.sqrt (A*Real.log h) := Real.sqrt_pos.mpr hAl
  have hsq := Real.sq_sqrt hAl.le
  obtain ⟨hw₁,hw₂⟩ := le_min_iff.mp hw
  have hclog : 0 < C₀*Real.log h := mul_pos hC hlog
  have hprod : 0 < Kmean*(h*hx) := by nlinarith only [hclog,hw₂,hk]
  have hhx : 0 < h*hx := (mul_pos_iff_of_pos_left hKm).mp hprod
  have hsize : (Real.sqrt (A*Real.log h))^2 ≤ h := by
    rw [hsq]
    exact (mul_le_mul_of_nonneg_right hCA hlog.le).trans hw₁
  have hTle : Real.sqrt (A*Real.log h) ≤ h := by nlinarith [sq_nonneg (h-1)]
  have hcSq : (16*Real.sqrt (A*Real.log h))^2 < (ρ*Real.sqrt h)^2 := by
    rw [mul_pow,mul_pow,hsq,Real.sq_sqrt hh0.le]
    have hcLog := mul_lt_mul_of_pos_right hcompact hlog
    have hcWin := mul_le_mul_of_nonneg_left hw₁ hρsq.le
    nlinarith only [hcLog,hcWin]
  have hoSq : (16*Real.sqrt (A*Real.log h))^2 < (ρ*Real.sqrt (h*hx))^2 := by
    rw [mul_pow,mul_pow,hsq,Real.sq_sqrt hhx.le]
    have hoLog := mul_lt_mul_of_pos_right horigin hlog
    have hoWin := mul_le_mul_of_nonneg_left (hw₂.trans hk) hρsq.le
    have hcancel : Kmean*(256*A*Real.log h) < Kmean*(ρ^2*(h*hx)) := by
      nlinarith only [hoLog,hoWin]
    nlinarith only [hcancel,hKm]
  refine ⟨hT,hsq,hsize,hTle,?_,?_⟩
  · nlinarith [mul_pos hρ (Real.sqrt_pos.mpr hh0)]
  · nlinarith [mul_pos hρ (Real.sqrt_pos.mpr hhx)]

end WP.Analysis
