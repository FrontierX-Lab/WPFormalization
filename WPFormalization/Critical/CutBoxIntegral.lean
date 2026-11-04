import Mathlib
/-! The physical edge-length box and a direct finite-dimensional Lebesgue integral bound, used in the actual Mirzakhani orbit integral. -/

noncomputable section
namespace WP.Critical
open MeasureTheory Set Finset
open scoped ENNReal

/-- The common physical-length box, on the actual r-dimensional edge space. -/
def cutLengthBox (r:ℕ) (L:ℝ) : Set (Fin r→ℝ) := Icc (fun _=>0) (fun _=>L)

def cutLengthTest (r:ℕ) (L:ℝ) : (Fin r→ℝ)→ℝ≥0∞ :=
  (cutLengthBox r L).indicator (fun _=>1)

lemma cutLengthTest_measurable (r:ℕ) (L:ℝ) : Measurable (cutLengthTest r L) :=
  measurable_const.indicator measurableSet_Icc

lemma cut_box_integral_envelope (r:ℕ) (L U:ℝ) (hL:0≤L) (hU:0≤U)
    (V:(Fin r→ℝ)→ℝ) (hV:∀x∈cutLengthBox r L,V x≤U) :
    (∫⁻x:Fin r→ℝ in {x|∀i,0≤x i},
      cutLengthTest r L x*ENNReal.ofReal (V x)*(∏i,ENNReal.ofReal (x i))) ≤
        ENNReal.ofReal (U*L^(2*r)) := by
  have hpoint (x:Fin r→ℝ) :
      cutLengthTest r L x*ENNReal.ofReal (V x)*(∏i,ENNReal.ofReal (x i)) ≤
        (cutLengthBox r L).indicator (fun _=>ENNReal.ofReal (U*L^r)) x := by
    by_cases hx:x∈cutLengthBox r L
    · have hx0:∀i,0≤x i := hx.1
      have hxL:∀i,x i≤L := hx.2
      rw [cutLengthTest,indicator_of_mem hx,one_mul,indicator_of_mem hx]
      have hprod : (∏i,ENNReal.ofReal (x i))≤ENNReal.ofReal (L^r) := by
        rw [←ENNReal.ofReal_prod_of_nonneg (fun i _=>hx0 i)]
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ ∏_i:Fin r,L := prod_le_prod₀ (fun i _=>hx0 i) (fun i _=>hxL i)
          _ = _ := by simp
      exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (hV x hx)) hprod).trans_eq
        (ENNReal.ofReal_mul hU).symm
    · simp only [cutLengthTest,indicator_of_notMem hx,zero_mul]
      exact zero_le
  calc
    _ ≤ ∫⁻x:Fin r→ℝ,cutLengthTest r L x*ENNReal.ofReal (V x)*(∏i,ENNReal.ofReal (x i)) :=
      lintegral_mono' Measure.restrict_le_self (fun _=>le_rfl)
    _ ≤ ∫⁻x:Fin r→ℝ,(cutLengthBox r L).indicator (fun _=>ENNReal.ofReal (U*L^r)) x :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal (U*L^r)*volume (cutLengthBox r L) :=
      lintegral_indicator_const measurableSet_Icc _
    _ = _ := by
      rw [cutLengthBox,Real.volume_Icc_pi]
      simp only [sub_zero,prod_const,card_univ,Fintype.card_fin]
      rw [←ENNReal.ofReal_pow hL,←ENNReal.ofReal_mul (by positivity:0≤U*L^r)]
      congr 1
      rw [mul_assoc,←pow_add,show r+r=2*r by omega]

end WP.Critical
