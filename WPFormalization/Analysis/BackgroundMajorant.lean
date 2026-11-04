import WPFormalization.Intersection.ShiftedRecursion
import Mathlib
noncomputable section
open scoped BigOperators
namespace WP.Analysis

lemma background_size_le {m : ℕ} (l : Fin m → ℕ) (hl : l ∈ backgrounds m) :
    ∑ i, l i ≤ m := by
  calc
    _ ≤ ∑ i : Fin m, (i.val+1)*l i :=
      Finset.sum_le_sum fun i _ => by nlinarith [Nat.zero_le (i.val * l i)]
    _ = m := WP.mem_backgrounds_iff m l |>.mp hl

lemma ascFactorial_real_le (h m k : ℕ) (hh : 1 ≤ h) (hk : k ≤ m) :
    (h.ascFactorial k : ℝ) ≤ ((h:ℝ)+m)^k := by
  have ha := Nat.ascFactorial_le_pow_add (h-1) k
  have he : h-1+1=h := by omega
  rw [he] at ha
  have hb : h-1+k ≤ h+m := by omega
  exact_mod_cast ha.trans (Nat.pow_le_pow_left hb k)

lemma scaled_background_product {m : ℕ} (l : Fin m → ℕ) (x : Fin m → ℝ)
    (C : ℝ) (hC : C ≠ 0) :
    C ^ (∑ i, (i.val+1)*l i) *
      ∏ i, ((x i / C^(i.val+1))^(l i) / (l i).factorial) =
      ∏ i, (x i)^(l i) / (l i).factorial := by
  rw [← Finset.prod_pow_eq_pow_sum]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [pow_mul, div_pow]
  field_simp

lemma asc_product_le {m : ℕ} (h : ℕ) (hh : 1 ≤ h) (l : Fin m → ℕ)
    (hl : l ∈ backgrounds m) (b : Fin m → ℝ) :
    (h.ascFactorial (∑ i, l i):ℝ) *
      ∏ i, |b i|^(l i) / (l i).factorial ≤
      ∏ i, (((h:ℝ)+m)*|b i|)^(l i) / (l i).factorial := by
  calc
    _ ≤ (((h:ℝ)+m)^(∑ i, l i)) *
        ∏ i, |b i|^(l i) / (l i).factorial := by
      apply mul_le_mul_of_nonneg_right
      · exact ascFactorial_real_le h m _ hh (background_size_le l hl)
      · exact Finset.prod_nonneg fun i _ => by positivity
    _ = _ := by
      simp_rw [mul_pow, Finset.prod_div_distrib, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
      ring

lemma finite_box_exp (m : ℕ) (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ l : Fin m → Fin (m+1), ∏ i, (x i)^(l i).val / ((l i).val).factorial) ≤
      Real.exp (∑ i, x i) := by
  rw [← Fintype.prod_sum (fun (i : Fin m) (j : Fin (m+1)) =>
    (x i)^j.val / j.val.factorial), Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro i _
    exact Finset.sum_nonneg fun j _ =>
      div_nonneg (pow_nonneg (hx i) _) (Nat.cast_nonneg _)
  · intro i _
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => (x i)^n / (n.factorial:ℝ))]
    exact Real.sum_le_exp_of_nonneg (hx i) (m+1)

lemma background_sum_exp (m : ℕ) (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ l ∈ backgrounds m, ∏ i, (x i)^(l i) / (l i).factorial) ≤
      Real.exp (∑ i, x i) := by
  let box : Finset (Fin m → ℕ) := Finset.univ.image
    (fun l : Fin m → Fin (m+1) => fun i => (l i).val)
  calc
    _ ≤ ∑ l ∈ box, ∏ i, (x i)^(l i) / (l i).factorial := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro l _ _
        exact Finset.prod_nonneg fun i _ =>
          div_nonneg (pow_nonneg (hx i) _) (Nat.cast_nonneg _)
    _ = ∑ l : Fin m → Fin (m+1), ∏ i, (x i)^(l i).val / ((l i).val).factorial := by
      unfold box
      rw [Finset.sum_image]
      intro f _ g _ hfg
      funext i
      exact Fin.ext (congrFun hfg i)
    _ ≤ _ := finite_box_exp m x hx

lemma geometric_half_fin (m : ℕ) :
    (∑ i : Fin m, (1/2:ℝ)^(i.val+1)) ≤ 1 := by
  simp_rw [pow_succ]
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range]
  have hh := sum_geometric_two_le m
  linarith

lemma normalized_background_factor (S B : ℝ) (hS : 0 ≤ S) (hB : 1 ≤ B)
    (j : ℕ) (b : ℝ) (hb : |b| ≤ B^j) :
    S*|b|/(2*B)^j ≤ S*(1/2:ℝ)^j := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hden : 0 < (2*B)^j := pow_pos (by positivity) _
  apply (div_le_iff₀ hden).2
  calc
    S*|b| ≤ S*B^j := mul_le_mul_of_nonneg_left hb hS
    _ = _ := by
      simp only [mul_pow, div_pow, one_pow]
      field_simp

lemma background_ascending_majorant (h m : ℕ) (hh : 1 ≤ h) (B : ℝ) (hB : 1 ≤ B)
    (b : Fin m → ℝ) (hb : ∀ i, |b i| ≤ B^(i.val+1)) :
    (∑ l ∈ backgrounds m, (h.ascFactorial (∑ i, l i):ℝ) *
      ∏ i, |b i|^(l i) / (l i).factorial) ≤
      (2*B)^m * Real.exp ((h:ℝ)+m) := by
  let S : ℝ := (h:ℝ)+m
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC : 0 < 2*B := by linarith
  calc
    _ ≤ ∑ l ∈ backgrounds m, ∏ i, (S*|b i|)^(l i)/(l i).factorial := by
      exact Finset.sum_le_sum fun l hl => asc_product_le h hh l hl b
    _ = (2*B)^m * ∑ l ∈ backgrounds m,
          ∏ i, (S*|b i|/(2*B)^(i.val+1))^(l i)/(l i).factorial := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      have he := scaled_background_product l (fun i => S*|b i|) (2*B) hC.ne'
      rw [WP.mem_backgrounds_iff m l |>.mp hl] at he
      exact he.symm
    _ ≤ (2*B)^m * Real.exp
          (∑ i, S*|b i|/(2*B)^(i.val+1)) := by
      apply mul_le_mul_of_nonneg_left
      · exact background_sum_exp m _ fun i => by positivity
      · positivity
    _ ≤ (2*B)^m * Real.exp S := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ ∑ i : Fin m, S*(1/2:ℝ)^(i.val+1) := by
          exact Finset.sum_le_sum fun i _ => normalized_background_factor S B hS hB _ _ (hb i)
        _ = S * ∑ i : Fin m, (1/2:ℝ)^(i.val+1) := by rw [Finset.mul_sum]
        _ ≤ S := by nlinarith [geometric_half_fin m]
end WP.Analysis
