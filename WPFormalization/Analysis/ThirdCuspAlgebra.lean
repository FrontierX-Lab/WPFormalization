import Mathlib

/-! Second-order change from child to parent complexity with a cubic error. -/

noncomputable section
open Set Filter

noncomputable section
namespace WP.Analysis
lemma third_cusp_change_complexity (x a b e h c B E : ℝ)
    (hh : 1 ≤ h) (hc : 0 ≤ c) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hb : |b| ≤ B) (he : |e| ≤ E)
    (hx : |x-(a-b/(h+1)+e/(h+1)^2)| ≤ c/(h+1)^3) :
    |x-(a-b/h+(b+e)/h^2)| ≤ (c+B+3*E)/h^3 := by
  have hp : 0<h := lt_of_lt_of_le zero_lt_one hh
  have hplus : 0<h+1 := by linarith
  have hraw : c/(h+1)^3 ≤ c/h^3 :=
    div_le_div_of_nonneg_left hc (pow_pos hp 3) (pow_le_pow_left₀ hp.le (by linarith) 3)
  have hbterm : |b/(h^2*(h+1))| ≤ B/h^3 := by
    rw [abs_div,abs_of_pos (by positivity : 0<h^2*(h+1))]
    calc
      _ ≤ B/(h^2*(h+1)) := div_le_div_of_nonneg_right hb (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left hB (pow_pos hp 3) (by nlinarith [sq_nonneg h])
  have heterm : |e*(2*h+1)/(h^2*(h+1)^2)| ≤ 3*E/h^3 := by
    rw [abs_div,abs_mul,abs_of_nonneg (by linarith : 0 ≤ 2*h+1),abs_of_pos (by positivity : 0<h^2*(h+1)^2)]
    calc
      _ ≤ E*(2*h+1)/(h^2*(h+1)^2) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right he (by linarith)) (by positivity)
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity : 0<h^2*(h+1)^2) (pow_pos hp 3)).2
        have hs : h*(2*h+1) ≤ 3*(h+1)^2 := by nlinarith [sq_nonneg h]
        have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ E*h^2 by positivity)
        nlinarith
  have heq : x-(a-b/h+(b+e)/h^2)=
      (x-(a-b/(h+1)+e/(h+1)^2))-b/(h^2*(h+1))-e*(2*h+1)/(h^2*(h+1)^2) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |x-(a-b/(h+1)+e/(h+1)^2)|+|b/(h^2*(h+1))|+|e*(2*h+1)/(h^2*(h+1)^2)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ c/h^3+B/h^3+3*E/h^3 := add_le_add (add_le_add (hx.trans hraw) hbterm) heterm
    _ = _ := by ring
end WP.Analysis
