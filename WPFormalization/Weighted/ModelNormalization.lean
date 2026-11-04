import WPFormalization.Statements.Comparison
import WPFormalization.Analysis.HarmonicPositivity
/-! Exact harmonic-model merger, contraction, and separating normalization.
The coefficient denominator is nonzero by the existing closed-parameter
harmonic positivity theorem. No uniform linear-mass estimate is assumed.
This module imports Comparison, so Weighted can use it without a cycle. -/
noncomputable section
namespace WP
lemma model_eq_coefficient_div_scale (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (Y : ℝ) :
    model g d Y = harmonicCoeff Y (complexity g d.length) (deficit g d)/primitiveScale g d.length := by
  unfold model primitiveScale
  field_simp
lemma model_merger_ratio (g : ℕ) (parent child : List ℕ) (l : ℕ) (Y : ℝ)
    (hh : 2 ≤ complexity g parent.length)
    (hc : complexity g child.length+1 = complexity g parent.length)
    (hdef : deficit g child = deficit g parent-l) (hY : Y ∈ Set.Icc 0 y₀) :
    theta Y l*model g child Y/model g parent Y =
      linearQ Y (complexity g parent.length) (deficit g parent) l /
        (3*((complexity g parent.length : ℝ)-1)) := by
  have hchild : 0 < complexity g child.length := by omega
  have hchildR : (0 : ℝ) < complexity g child.length := by exact_mod_cast hchild
  have hcoeff := harmonicCoeff_pos Y (complexity g parent.length) (deficit g parent) (by omega) hY
  have hspar : Stable g parent.length := by unfold Stable; unfold complexity at hh; omega
  have hschild : Stable g child.length := by unfold Stable; unfold complexity at hchild; omega
  rw [model_eq_coefficient_div_scale g parent hspar Y,
    model_eq_coefficient_div_scale g child hschild Y]
  unfold linearQ
  rw [hdef]
  have hscale : primitiveScale g parent.length =
      (1/(3*((complexity g parent.length : ℝ)-1)))*primitiveScale g child.length := by
    unfold primitiveScale
    rw [← hc,pow_succ,Nat.cast_add,Nat.cast_one,Real.Gamma_add_one hchildR.ne']
    field_simp [hchildR.ne',(Real.Gamma_pos_of_pos hchildR).ne']
    <;> ring
  rw [hscale,show complexity g parent.length-1=complexity g child.length by omega]
  have hs : primitiveScale g child.length ≠ 0 := (primitiveScale_pos g child.length hschild).ne'
  have hH : (0 : ℝ) < (complexity g parent.length : ℝ)-1 := by
    rw [← hc,Nat.cast_add,Nat.cast_one]
    linarith
  field_simp [hs,hcoeff.ne',hH.ne']
  <;> ring
lemma model_contraction_ratio (g : ℕ) (parent child : List ℕ) (l : ℕ) (Y : ℝ)
    (hg : 1 ≤ g) (hh : 2 ≤ complexity g parent.length)
    (hc : complexity (g-1) child.length+1 = complexity g parent.length)
    (hdef : deficit (g-1) child = deficit g parent-l) (hY : Y ∈ Set.Icc 0 y₀) :
    theta Y l*model (g-1) child Y/model g parent Y =
      4*linearQ Y (complexity g parent.length) (deficit g parent) l /
        (3*((complexity g parent.length : ℝ)-1)) := by
  have hchild : 0 < complexity (g-1) child.length := by omega
  have hchildR : (0 : ℝ) < complexity (g-1) child.length := by exact_mod_cast hchild
  have hcoeff := harmonicCoeff_pos Y (complexity g parent.length) (deficit g parent) (by omega) hY
  have hspar : Stable g parent.length := by unfold Stable; unfold complexity at hh; omega
  have hschild : Stable (g-1) child.length := by unfold Stable; unfold complexity at hchild; omega
  rw [model_eq_coefficient_div_scale g parent hspar Y,
    model_eq_coefficient_div_scale (g-1) child hschild Y]
  unfold linearQ
  rw [hdef]
  have h4 : (4 : ℝ)^g = 4^(g-1)*4 := by
    nth_rw 1 [show g=(g-1)+1 by omega]
    rw [pow_succ]
  have hscale : primitiveScale g parent.length =
      (4/(3*((complexity g parent.length : ℝ)-1)))*primitiveScale (g-1) child.length := by
    unfold primitiveScale
    rw [← hc,pow_succ,Nat.cast_add,Nat.cast_one,Real.Gamma_add_one hchildR.ne',h4]
    field_simp [hchildR.ne',(Real.Gamma_pos_of_pos hchildR).ne']
    <;> ring
  rw [hscale,show complexity g parent.length-1=complexity (g-1) child.length by omega]
  have hs : primitiveScale (g-1) child.length ≠ 0 := (primitiveScale_pos (g-1) child.length hschild).ne'
  have hH : (0 : ℝ) < (complexity g parent.length : ℝ)-1 := by
    rw [← hc,Nat.cast_add,Nat.cast_one]
    linarith
  field_simp [hs,hcoeff.ne',hH.ne']
  <;> ring
lemma model_separating_ratio (g g₁ g₂ : ℕ) (parent child₁ child₂ : List ℕ) (l : ℕ) (Y : ℝ)
    (hg : g₁+g₂=g) (hh : 1 ≤ complexity g parent.length)
    (hc : complexity g₁ child₁.length+complexity g₂ child₂.length+1 = complexity g parent.length)
    (hY : Y ∈ Set.Icc 0 y₀) :
    theta Y l/2*model g₁ child₁ Y*model g₂ child₂ Y/model g parent Y =
      theta Y l/6*(Real.Gamma (complexity g₁ child₁.length)*Real.Gamma (complexity g₂ child₂.length)/
        Real.Gamma (complexity g parent.length))*
        (harmonicCoeff Y (complexity g₁ child₁.length) (deficit g₁ child₁)*
          harmonicCoeff Y (complexity g₂ child₂.length) (deficit g₂ child₂)/
          harmonicCoeff Y (complexity g parent.length) (deficit g parent)) := by
  have hcoeff := harmonicCoeff_pos Y (complexity g parent.length) (deficit g parent) (by omega) hY
  have hhR : (0 : ℝ) < complexity g parent.length := by exact_mod_cast (show 0 < complexity g parent.length by omega)
  have hG := (Real.Gamma_pos_of_pos hhR).ne'
  have hpow₃ : (3 : ℝ)^(complexity g parent.length) =
      3^(complexity g₁ child₁.length)*3^(complexity g₂ child₂.length)*3 := by
    rw [← hc,pow_succ,pow_add]
  have hpow₄ : (4 : ℝ)^g = 4^g₁*4^g₂ := by rw [← hg,pow_add]
  unfold model
  rw [hpow₃,hpow₄]
  field_simp [hG,hcoeff.ne']
  <;> ring
end WP
