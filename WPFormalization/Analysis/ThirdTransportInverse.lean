import Mathlib

/-! A genuine second-order inverse-ratio expansion with an explicit uniform quadratic remainder. -/

noncomputable section
open Set

noncomputable section
namespace WP.Analysis
lemma third_order_ratio_inverse (u A b k h c a B D F : ℝ)
    (hh : 1 ≤ h) (ha : 0<a) (hu : a/2 ≤ u) (hc : 0 ≤ c)
    (hA : |A| ≤ B) (hb : |b| ≤ D) (hk : |k| ≤ F)
    (he : |u-A*(1-b/h+k/h^2)| ≤ c/h^3) :
    |A*h/u-(h+b+(b^2-k)/h)| ≤
      ((2/a)*(B*D*((D^2+F)+F)+B*F*(D^2+F)+c*(1+D+(D^2+F))))/h^2 := by
  have hp : 0<h := lt_of_lt_of_le zero_lt_one hh
  have hup : 0<u := by linarith
  have hB : 0 ≤ B := (abs_nonneg _).trans hA
  have hD : 0 ≤ D := (abs_nonneg _).trans hb
  have hF : 0 ≤ F := (abs_nonneg _).trans hk
  let G : ℝ := D^2+F
  have hG : 0 ≤ G := by dsimp [G];positivity
  have hgamma : |b^2-k| ≤ G := by
    calc
      _ ≤ |b^2|+|k| := abs_sub _ _
      _ ≤ D^2+F := by rw [abs_pow];exact add_le_add (pow_le_pow_left₀ (abs_nonneg _) hb 2) hk
  have hdiff : |(b^2-k)-k| ≤ G+F := (abs_sub _ _).trans (add_le_add hgamma hk)
  have htarget : |h+b+(b^2-k)/h| ≤ h*(1+D+G) := by
    calc
      _ ≤ |h|+|b|+|(b^2-k)/h| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ h+D+G/h := by rw [abs_of_pos hp,abs_div,abs_of_pos hp];exact add_le_add (add_le_add le_rfl hb) (div_le_div_of_nonneg_right hgamma hp.le)
      _ ≤ h+D+G := by gcongr;exact div_le_self hG hh
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hh) hD,mul_nonneg (sub_nonneg.mpr hh) hG]
  have hfirst : |A*b*((b^2-k)-k)/h^2| ≤ B*D*(G+F)/h^2 := by
    rw [abs_div,abs_pow,abs_of_pos hp,abs_mul,abs_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul
      (mul_le_mul hA hb (abs_nonneg _) hB) hdiff (abs_nonneg _) (mul_nonneg hB hD)) (sq_nonneg h)
  have hsecond : |A*k*(b^2-k)/h^3| ≤ B*F*G/h^2 := by
    rw [abs_div,abs_pow,abs_of_pos hp,abs_mul,abs_mul]
    calc
      _ ≤ B*F*G/h^3 := div_le_div_of_nonneg_right (mul_le_mul
        (mul_le_mul hA hk (abs_nonneg _) hB) hgamma (abs_nonneg _) (mul_nonneg hB hF)) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hp) (by nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg h)])
  have herr : |(h+b+(b^2-k)/h)*(u-A*(1-b/h+k/h^2))| ≤ c*(1+D+G)/h^2 := by
    rw [abs_mul]
    calc
      _ ≤ (h*(1+D+G))*(c/h^3) := mul_le_mul htarget he (abs_nonneg _) (by positivity)
      _ = _ := by field_simp <;> ring
  have heq : A*h/u-(h+b+(b^2-k)/h)=
      (A*b*((b^2-k)-k)/h^2-A*k*(b^2-k)/h^3-
        (h+b+(b^2-k)/h)*(u-A*(1-b/h+k/h^2)))/u := by field_simp <;> ring
  have hnum : |A*b*((b^2-k)-k)/h^2-A*k*(b^2-k)/h^3-
      (h+b+(b^2-k)/h)*(u-A*(1-b/h+k/h^2))| ≤
      (B*D*(G+F)+B*F*G+c*(1+D+G))/h^2 := by
    calc
      _ ≤ |A*b*((b^2-k)-k)/h^2|+|A*k*(b^2-k)/h^3|+
          |(h+b+(b^2-k)/h)*(u-A*(1-b/h+k/h^2))| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ B*D*(G+F)/h^2+B*F*G/h^2+c*(1+D+G)/h^2 := add_le_add (add_le_add hfirst hsecond) herr
      _ = _ := by ring
  rw [heq,abs_div,abs_of_pos hup]
  calc
    _ ≤ ((B*D*(G+F)+B*F*G+c*(1+D+G))/h^2)/u := div_le_div_of_nonneg_right hnum hup.le
    _ ≤ ((B*D*(G+F)+B*F*G+c*(1+D+G))/h^2)/(a/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hu
    _ = _ := by dsimp [G];field_simp <;> ring
end WP.Analysis
