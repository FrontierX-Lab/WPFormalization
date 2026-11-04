import WPFormalization.Statements.Basic
/-! Patching a cubic critical window to a logarithmic long-interval estimate, with constants uniform in the physical parameter. -/
noncomputable section
namespace WP.Analysis
open Set
lemma cubic_window_patching (p : ℕ) (f : ℕ → ℝ → ℝ)
    (hshort : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico (0:ℝ) y₀,
      y₀-Y ≤ 1/(complexity g p:ℝ)^3 → |f g Y| ≤ C/(g:ℝ)^2)
    (hlong : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G,
      let h : ℝ := complexity g p
      let B : ℝ := y₀-(h⁻¹)^3
      B ∈ Ico (0:ℝ) y₀ ∧ ∀ Y ∈ Ico (0:ℝ) y₀, Y ≤ B →
        |f g Y-f g B| ≤ C*Real.log ((g:ℝ)+1)/(g:ℝ)^2) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico (0:ℝ) y₀,
      |f g Y| ≤ C*Real.log ((g:ℝ)+1)/(g:ℝ)^2 := by
  obtain ⟨Cs,hCs,Gs,hshort⟩ := hshort
  obtain ⟨Cl,hCl,Gl,hlong⟩ := hlong
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := Cl+Cs/Real.log 2
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨C,hC,Gs+Gl+2,?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := by omega
  have hg0 : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  have hh : 0 < (complexity g p:ℝ) := by exact_mod_cast (show 0 < complexity g p by unfold complexity;omega)
  let B : ℝ := y₀-((complexity g p:ℝ)⁻¹)^3
  obtain ⟨hB,hvariation⟩ := hlong g (by omega)
  have hloglower : Real.log 2 ≤ Real.log ((g:ℝ)+1) := Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ g+1 by omega))
  have hscale : Cs/(g:ℝ)^2 ≤ (Cs/Real.log 2)*Real.log ((g:ℝ)+1)/(g:ℝ)^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    calc
      _ = (Cs/Real.log 2)*Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hloglower (by positivity)
  have hlog0 : 0 ≤ Real.log ((g:ℝ)+1) := hl2.le.trans hloglower
  by_cases hYB : Y ≤ B
  · have hBsmall : y₀-B ≤ 1/(complexity g p:ℝ)^3 := by dsimp [B];simp only [sub_sub_cancel,one_div,inv_pow];rfl
    have hanchor := hshort g (by omega) B hB hBsmall
    calc
      _ ≤ |f g Y-f g B|+|f g B| := by simpa only [sub_zero] using (abs_sub_le (f g Y) (f g B) 0)
      _ ≤ Cl*Real.log ((g:ℝ)+1)/(g:ℝ)^2+Cs/(g:ℝ)^2 := add_le_add (hvariation Y hY hYB) hanchor
      _ ≤ Cl*Real.log ((g:ℝ)+1)/(g:ℝ)^2+(Cs/Real.log 2)*Real.log ((g:ℝ)+1)/(g:ℝ)^2 := add_le_add le_rfl hscale
      _ = _ := by dsimp [C];ring
  · have hsmall : y₀-Y ≤ 1/(complexity g p:ℝ)^3 := by
      have hi : y₀-B=1/(complexity g p:ℝ)^3 := by dsimp [B];simp [one_div,inv_pow]
      rw [←hi]
      linarith
    calc
      _ ≤ Cs/(g:ℝ)^2 := hshort g (by omega) Y hY hsmall
      _ ≤ (Cs/Real.log 2)*Real.log ((g:ℝ)+1)/(g:ℝ)^2 := hscale
      _ ≤ _ := by
        have hc := div_nonneg (mul_nonneg hCl.le hlog0) (sq_nonneg (g:ℝ))
        dsimp [C]
        rw [add_mul,add_div]
        linarith
end WP.Analysis
