import WPFormalization.Statements.Basic

/-! The scalar majorant and induction closure arithmetic in Appendix B.
The real-variable extension agrees with the paper's F at positive integer complexity.
These results do not assert that arbitrary intersection numbers satisfy the majorant. -/
namespace WP

noncomputable def primitiveMajorant (h : ℝ) : ℝ :=
  if h ≤ 7 then 1/3 else 1-4/(h-1)

lemma primitiveMajorant_of_ge_seven {h : ℝ} (hh : 7 ≤ h) :
    primitiveMajorant h = 1-4/(h-1) := by
  by_cases he : h ≤ 7
  · have : h = 7 := le_antisymm he hh
    subst h
    norm_num [primitiveMajorant]
  · simp [primitiveMajorant, he]

lemma primitiveMajorant_nonneg (h : ℝ) : 0 ≤ primitiveMajorant h := by
  by_cases hh : h ≤ 7
  · norm_num [primitiveMajorant, hh]
  · simp only [primitiveMajorant, if_neg hh]
    have hfrac : 4/(h-1) ≤ 1 := (div_le_iff₀ (by linarith : 0 < h-1)).2 (by linarith)
    linarith

lemma primitiveMajorant_le_one (h : ℝ) : primitiveMajorant h ≤ 1 := by
  by_cases hh : h ≤ 7
  · norm_num [primitiveMajorant, hh]
  · simp only [primitiveMajorant, if_neg hh]
    have hpos : 0 < h-1 := by linarith
    have : 0 ≤ 4/(h-1) := by positivity
    linarith

lemma primitiveMajorant_monotone : Monotone primitiveMajorant := by
  intro h k hhk
  by_cases hk : k ≤ 7
  · simp [primitiveMajorant, hk, le_trans hhk hk]
  · by_cases hh : h ≤ 7
    · simp only [primitiveMajorant, if_pos hh, if_neg hk]
      have hfrac : 4/(k-1) ≤ 2/3 :=
        (div_le_iff₀ (by linarith : 0 < k-1)).2 (by linarith)
      linarith
    · simp only [primitiveMajorant, if_neg hh, if_neg hk]
      have hfrac : 4/(k-1) ≤ 4/(h-1) :=
        (div_le_div_iff₀ (by linarith : 0 < k-1) (by linarith : 0 < h-1)).2 (by nlinarith)
      linarith

lemma primitiveMajorant_increment {h : ℝ} (hh : 8 ≤ h) :
    primitiveMajorant h-primitiveMajorant (h-1) = 4/((h-1)*(h-2)) := by
  rw [primitiveMajorant_of_ge_seven (by linarith), primitiveMajorant_of_ge_seven (by linarith)]
  have hpos₁ : 0 < h-1 := by linarith
  have hpos₂ : 0 < h-2 := by linarith
  have hpos₃ : 0 < h-3 := by linarith
  have hpos₄ : 0 < h-4 := by linarith
  have hnon8 : 0 ≤ h-8 := by linarith
  have h₁ : h-1 ≠ 0 := by linarith
  have h₂ : h-2 ≠ 0 := by linarith
  simp only [show h-1-1 = h-2 by ring]
  field_simp [h₁, h₂] <;> ring

lemma primitiveMajorant_one_zero {Z : ℝ} (hZ : 2 ≤ Z) :
    (1+2/(3*(Z-1)))*primitiveMajorant (Z-1) ≤ 1 := by
  by_cases hh : Z ≤ 8
  · have hf : primitiveMajorant (Z-1) = 1/3 := by simp [primitiveMajorant, show Z-1 ≤ 7 by linarith]
    rw [hf]
    have hfrac : 2/(3*(Z-1)) ≤ 2/3 :=
      (div_le_iff₀ (by nlinarith : 0 < 3*(Z-1))).2 (by nlinarith)
    linarith
  · rw [primitiveMajorant_of_ge_seven (by linarith)]
    have hpos₁ : 0 < Z-1 := by linarith
    have hpos₂ : 0 < Z-2 := by linarith
    have hposZ : 0 < Z := by linarith
    simp only [show Z-1-1 = Z-2 by ring]
    have h₁ : Z-1 ≠ 0 := by linarith
    have h₂ : Z-2 ≠ 0 := by linarith
    have he : (1+2/(3*(Z-1)))*(1-4/(Z-2))-1 =
        -(10*Z)/(3*(Z-1)*(Z-2)) := by field_simp [h₁, h₂]; ring
    have hn : 0 ≤ (10*Z)/(3*(Z-1)*(Z-2)) := by positivity
    rw [neg_div] at he
    linarith

lemma primitive_high_degree_excess {h : ℝ} (hh : 8 ≤ h) :
    8/(9*(h-1)*(h-3))+2/((h-1)*(h-2)) ≤ 46/(15*(h-1)*(h-2)) ∧
    46/(15*(h-1)*(h-2)) < 4/((h-1)*(h-2)) := by
  have hpos₁ : 0 < h-1 := by linarith
  have hpos₂ : 0 < h-2 := by linarith
  have hpos₃ : 0 < h-3 := by linarith
  have hpos₄ : 0 < h-4 := by linarith
  have hnon8 : 0 ≤ h-8 := by linarith
  have h₁ : h-1 ≠ 0 := by linarith
  have h₂ : h-2 ≠ 0 := by linarith
  have h₃ : h-3 ≠ 0 := by linarith
  have he : 46/(15*(h-1)*(h-2))-
      (8/(9*(h-1)*(h-3))+2/((h-1)*(h-2))) =
      8*(h-8)/(45*(h-1)*(h-2)*(h-3)) := by field_simp [h₁, h₂, h₃]; ring
  have hn : 0 ≤ 8*(h-8)/(45*(h-1)*(h-2)*(h-3)) := by positivity
  constructor
  · linarith
  · have hp : 0 < (14/15 : ℝ)/((h-1)*(h-2)) := by positivity
    have he' : 4/((h-1)*(h-2))-46/(15*(h-1)*(h-2)) =
        (14/15 : ℝ)/((h-1)*(h-2)) := by field_simp [h₁, h₂]; ring
    linarith

noncomputable def doubleZeroStringFactor (h : ℝ) : ℝ :=
  (3*h-5)*(3*h-10)/((3*h-6)*(3*h-12))

lemma primitive_low_degree_excess {h : ℝ} (hh : 8 ≤ h) :
    2*(doubleZeroStringFactor h-1)/(3*(h-1)) =
      2*(9*h-22)/(27*(h-4)*(h-1)*(h-2)) ∧
    2*(doubleZeroStringFactor h-1)/(3*(h-1)) ≤ 25/(27*(h-1)*(h-2)) := by
  have hpos₁ : 0 < h-1 := by linarith
  have hpos₂ : 0 < h-2 := by linarith
  have hpos₃ : 0 < h-3 := by linarith
  have hpos₄ : 0 < h-4 := by linarith
  have hnon8 : 0 ≤ h-8 := by linarith
  have h₁ : h-1 ≠ 0 := by linarith
  have h₂ : h-2 ≠ 0 := by linarith
  have h₄ : h-4 ≠ 0 := by linarith
  have h₆ : 3*h-6 ≠ 0 := by linarith
  have h₁₂ : 3*h-12 ≠ 0 := by linarith
  have he : 2*(doubleZeroStringFactor h-1)/(3*(h-1)) =
      2*(9*h-22)/(27*(h-4)*(h-1)*(h-2)) := by
    unfold doubleZeroStringFactor
    field_simp [h₁, h₂, h₄, h₆, h₁₂] <;> ring
  constructor
  · exact he
  · rw [he]
    have he' : 25/(27*(h-1)*(h-2))-2*(9*h-22)/(27*(h-4)*(h-1)*(h-2)) =
        7*(h-8)/(27*(h-4)*(h-1)*(h-2)) := by field_simp [h₁, h₂, h₄]; ring
    have hp : 0 ≤ 7*(h-8)/(27*(h-4)*(h-1)*(h-2)) := by positivity
    linarith

lemma primitive_low_degree_closure {h : ℝ} (hh : 8 ≤ h) :
    2*(doubleZeroStringFactor h-1)/(3*(h-1))+2/((h-1)*(h-2)) <
      primitiveMajorant h-primitiveMajorant (h-1) := by
  rw [primitiveMajorant_increment hh]
  have hb := (primitive_low_degree_excess hh).2
  have hpos₁ : 0 < h-1 := by linarith
  have hpos₂ : 0 < h-2 := by linarith
  have hpos₃ : 0 < h-3 := by linarith
  have hpos₄ : 0 < h-4 := by linarith
  have hnon8 : 0 ≤ h-8 := by linarith
  have h₁ : h-1 ≠ 0 := by linarith
  have h₂ : h-2 ≠ 0 := by linarith
  have he : 25/(27*(h-1)*(h-2))+2/((h-1)*(h-2)) =
      79/(27*(h-1)*(h-2)) := by field_simp [h₁, h₂]; ring
  have hp : 0 < (29/27 : ℝ)/((h-1)*(h-2)) := by positivity
  have he' : 4/((h-1)*(h-2))-79/(27*(h-1)*(h-2)) =
      (29/27 : ℝ)/((h-1)*(h-2)) := by field_simp [h₁, h₂]; ring
  linarith

end WP
