import WPFormalization.Intersection.BackgroundRestriction
/-! The original normalized finite background sum as an exponential generating
sum in the rescaled background times. This identity uses no positivity or
unproved kernel input. -/
noncomputable section
namespace WP
lemma background_scale_product {M : ℕ} (h : ℕ) (t : Fin M → ℝ) (w l : Fin M → ℕ)
    (a r : ℝ) (ha : a ≠ 0) :
    a^h*r^(∑ i, w i*l i)*(∏ i, t i^(l i)/(l i).factorial)/a^(h+∑ i, l i) =
      ∏ i, (t i*r^(w i)/a)^(l i)/(l i).factorial := by
  simp only [mul_pow, div_pow, ← pow_mul, Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, pow_add]
  field_simp [ha]
  <;> ring
lemma normalized_background_sum_interior (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    normalized P g d Y =
      if Stable g d.length ∧ d.sum ≤ dimension g d.length then
        (d.map (fun k => (oddFactorial k : ℝ))).prod *
        ∑ l ∈ backgrounds (deficit g d), pure P g (d ++ backgroundDegrees l) *
          ∏ i : Fin (deficit g d),
            ((-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y)^(l i)/(l i).factorial
      else 0 := by
  have hy : Y ≠ y₀ := ne_of_lt hY.2
  have ha := a_ne_zero Y hY
  unfold normalized
  rw [if_neg hy]
  unfold shifted
  by_cases hs : Stable g d.length ∧ d.sum ≤ dimension g d.length
  · rw [if_pos hs, if_pos hs]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    have hd := (mem_backgrounds_iff (deficit g d) l).mp hl
    have he := background_scale_product (complexity g d.length)
      (fun i : Fin (deficit g d) => -(iteratedDeriv (i.val+2) X Y).re)
      (fun i : Fin (deficit g d) => i.val+1) l (a Y) (r Y) ha
    rw [hd] at he
    linear_combination ((d.map (fun k => (oddFactorial k : ℝ))).prod *
      pure P g (d ++ backgroundDegrees l))*he
  · simp [hs]
end WP
