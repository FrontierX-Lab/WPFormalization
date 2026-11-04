import WPFormalization.Marked.GrowingMarkingsLog
import WPFormalization.Analysis.GrowingMarkingScale

/-! Uniform sublinear logarithmic errors for marking counts growing as the square root of complexity. -/
noncomputable section
namespace WP
open Set
lemma W_growing_markings_log_small (P : PsiTheory) (M : ℝ) (hM : 0 < M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, ∀ g p : ℕ, 1 ≤ p → Stable g p → H ≤ complexity g p →
      (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) → ∀ Y ∈ Icc (0:ℝ) y₀,
      |Real.log (W P g p Y)-Real.log (Real.Gamma (complexity g p))+
        (complexity g p:ℝ)*Real.log (A Y)| ≤ ε*(g:ℝ) := by
  obtain ⟨C,hC,H₀,hbound⟩ := W_growing_markings_log_envelope P M hM
  obtain ⟨H₁,hH₁,hsmall⟩ := Analysis.sqrt_log_envelope_sublinear (ε/(4*C)) (by positivity)
  obtain ⟨N,hN⟩ := exists_nat_ge (max H₁ (4*M^2+1))
  refine ⟨max H₀ N,?_⟩
  intro g p hp hs hH hpM Y hY
  let h : ℝ := complexity g p
  have hhN : (N:ℝ) ≤ h := by dsimp [h];exact_mod_cast (le_max_right H₀ N).trans hH
  have hh₀ : H₀ ≤ complexity g p := (le_max_left _ _).trans hH
  have hh₁ : H₁ ≤ h := (le_max_left _ _).trans (hN.trans hhN)
  have hhM : 4*M^2+1 ≤ h := (le_max_right _ _).trans (hN.trans hhN)
  have hh0 : 0 ≤ h := by dsimp [h];positivity
  have hq : 2*M ≤ Real.sqrt h := by
    have hq0 := Real.sqrt_nonneg h
    nlinarith only [Real.sq_sqrt hh0,hhM,hM,hq0]
  have hcap : (p:ℝ) ≤ h/2 := by
    have he := mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg h)
    nlinarith only [he,Real.sq_sqrt hh0,hpM]
  have hcomp : h=2*(g:ℝ)+(p:ℝ)-2 := by
    dsimp [h,complexity]
    rw [Nat.cast_sub (by unfold Stable at hs;omega)]
    push_cast
    ring
  have hhg : h ≤ 4*(g:ℝ) := by linarith only [hcap,hcomp]
  have henv := hbound g p hp hs hh₀ hpM Y hY
  have he := mul_le_mul_of_nonneg_left (hsmall h hh₁) hC.le
  have hEq : C*(ε/(4*C)*h)=(ε/4)*h := by field_simp [hC.ne']
  rw [hEq] at he
  exact henv.trans (he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hhg hε.le]))
lemma complexity_le_four_genus_growing (g p : ℕ) (hs : Stable g p)
    (M : ℝ) (hM : 0 < M) (hp : (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ))
    (hlarge : 4*M^2+1 ≤ (complexity g p:ℝ)) :
    (complexity g p:ℝ) ≤ 4*g := by
  let h : ℝ := complexity g p
  have hh0 : 0 ≤ h := by dsimp [h];positivity
  have hq : 2*M ≤ Real.sqrt h := by
    nlinarith only [Real.sq_sqrt hh0,hlarge,hM,Real.sqrt_nonneg h]
  have hcap : (p:ℝ) ≤ h/2 := by
    have he := mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg h)
    nlinarith only [he,Real.sq_sqrt hh0,hp]
  have hcomp : h=2*(g:ℝ)+(p:ℝ)-2 := by
    dsimp [h,complexity]
    rw [Nat.cast_sub (by unfold Stable at hs;omega)]
    push_cast
    ring
  linarith only [hcap,hcomp]

end WP
