import WPFormalization.Analysis.LinearMassBounds
import WPFormalization.Weighted.ActiveDimension

/-! The full mass-to-square-root estimate for the second inequality of Lemma 5.5, independently of the first separating-mass bound. -/
noncomputable section
namespace WP
lemma separating_sqrt_scale (S h C M : ℝ) (L I : ℕ)
    (hC : 0≤C) (hM : 0≤M) (hh : 1≤h) (hI : I≤L)
    (hS : S≤M*Real.sqrt h) (hlarge : 6≤L → S≤M*h/L) :
    C*S*(1+(I : ℝ))/Real.rpow h (3/2 : ℝ) ≤ 6*C*M/Real.sqrt h := by
  have hh₀ : 0<h := by linarith
  have hs : 0<Real.sqrt h := Real.sqrt_pos_of_pos hh₀
  have hpow : Real.rpow h (3/2 : ℝ)=h*Real.sqrt h := by
    rw [Real.rpow_eq_pow,show (3/2 : ℝ)=1+1/2 by ring,Real.rpow_add hh₀,Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [hpow]
  apply (div_le_div_iff₀ (mul_pos hh₀ hs) hs).mpr
  have hIR : (I : ℝ)≤L := by exact_mod_cast hI
  by_cases hL : 6≤L
  · have hL₀ : (0 : ℝ)<L := by exact_mod_cast (show 0<L by omega)
    have hSL := hlarge hL
    have hSL' : S*(L : ℝ)≤M*h := (le_div_iff₀ hL₀).mp hSL
    have hR : 1+(I : ℝ)≤2*L := by
      have hLR : (6 : ℝ)≤L := by exact_mod_cast hL
      linarith
    have hprod := mul_le_mul_of_nonneg_left hSL' hC
    have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSL hC) (show 0≤1+(I : ℝ) by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hR (show 0≤C*(M*h/L) by positivity)
    have hbound : C*S*(1+(I : ℝ))≤2*C*M*h := by
      have he : C*(M*h/L)*(2*L)=2*C*M*h := by field_simp [hL₀.ne'] <;> ring
      linarith
    have hfinal := mul_le_mul_of_nonneg_right hbound hs.le
    nlinarith [show 0≤C*M*h*Real.sqrt h by positivity]
  · have hR : 1+(I : ℝ)≤6 := by
      have hLR : (L : ℝ)≤5 := by exact_mod_cast (show L≤5 by omega)
      linarith
    have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hC) (show 0≤1+(I : ℝ) by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hR (show 0≤C*(M*Real.sqrt h) by positivity)
    have hbound : C*S*(1+(I : ℝ))≤6*C*M*Real.sqrt h := by linarith
    have hfinal := mul_le_mul_of_nonneg_right hbound hs.le
    have hroot : Real.sqrt h≤h := by
      have hr := Real.sq_sqrt hh₀.le
      have hp := mul_nonneg (show 0≤h-1 by linarith) hh₀.le
      nlinarith [Real.sqrt_nonneg h]
    have hmul := mul_le_mul_of_nonneg_left hroot (show 0≤6*C*M*Real.sqrt h by positivity)
    nlinarith
lemma weightedSeparating_sqrt_envelope (C : ℝ) (hC : 0<C) :
    ∃ D : ℝ, 0<D ∧ ∀ g pivot : ℕ, ∀ d : List ℕ, 2≤g →
      (pivot::d).sum≤dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
      C*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot::d))*
        (1+inactive (pivot::d))/Real.rpow (complexity g (d.length+1)) (3/2 : ℝ) ≤
          D/Real.sqrt (complexity g (d.length+1)) := by
  obtain ⟨M,hM,hbound⟩ := linear_mass_bounds
  refine ⟨6*C*M,by positivity,?_⟩
  intro g pivot d hg hd Y hY
  have hh : 2≤complexity g (d.length+1) := by unfold complexity; omega
  have hhR : (1 : ℝ)≤complexity g (d.length+1) := by exact_mod_cast (show 1≤complexity g (d.length+1) by omega)
  have he := hbound g (pivot::d) (by simpa only [List.length_cons] using hh) (by simp)
    (by simpa only [List.length_cons] using hd) Y hY
  apply separating_sqrt_scale _ _ C M (2*(pivot::d).sum+(pivot::d).length) (inactive (pivot::d)) hC.le hM.le hhR
  · have hi := inactive_le_length (pivot::d)
    omega
  · simpa only [List.length_cons] using he.1
  · intro hL
    simpa only [List.length_cons,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using he.2 hL
end WP
