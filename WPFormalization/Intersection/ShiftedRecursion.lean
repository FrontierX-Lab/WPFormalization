import WPFormalization.Statements.IntersectionInterface
import WPFormalization.Analysis.Taylor
/-! Finite background combinatorics and the nilpotent kernel inversion needed
for the exact shifted DVV recursion. These are proved from the existing
intersection interface; the general shifted recursion is not assumed here. -/
noncomputable section
namespace WP
lemma normalized_unstable (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ)
    (hs : ¬ Stable g d.length) : normalized P g d Y = 0 := by
  by_cases hy : Y = y₀ <;> simp [normalized, shifted, hy, hs]
lemma normalized_excess (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ)
    (hd : dimension g d.length < d.sum) : normalized P g d Y = 0 := by
  have hn : ¬d.sum ≤ dimension g d.length := by omega
  by_cases hy : Y = y₀ <;> simp [normalized, shifted, hy, hn]
lemma normalized_top (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ)
    (hY : Y ∈ Set.Icc 0 y₀) (hd : d.sum = dimension g d.length) :
    normalized P g d Y = weighted P.psi g (d.map Int.ofNat) := by
  have hw : doubleWeight (d.map Int.ofNat) =
      (d.map (fun k => (oddFactorial k : ℝ))).prod := by
    simp [doubleWeight, List.map_map, Function.comp_def]
  unfold weighted
  rw [hw]
  by_cases hs : Stable g d.length
  · have hm : deficit g d = 0 := by simp [deficit, hd]
    by_cases hy : Y = y₀
    · simp [normalized, hy, hs, hd, hm, pure]
    · have hi : Y ∈ Set.Ico 0 y₀ := ⟨hY.1, lt_of_le_of_ne hY.2 hy⟩
      have ha := a_ne_zero Y hi
      rw [normalized, if_neg hy]
      unfold shifted
      rw [if_pos ⟨hs, hd.le⟩]
      generalize he : deficit g d = m
      have hzero : m = 0 := by omega
      clear hm he
      subst m
      simp [backgrounds_zero, backgroundDegrees, pure, ha]
      field_simp [ha]
      <;> ring
  · have hv : P.psi g (d.map Int.ofNat) = 0 :=
      P.vanish g _ (Or.inl (by simpa using hs))
    rw [normalized_unstable P g d Y hs, hv, mul_zero]
lemma triangle_sum_reindex {M : Type*} [AddCommMonoid M] (m : ℕ) (F : ℕ → ℕ → M) :
    (∑ l ∈ Finset.range (m+1), ∑ i ∈ Finset.range (m-l+1), F l i) =
    ∑ j ∈ Finset.range (m+1), ∑ l ∈ Finset.range (j+1), F l (j-l) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => ⟨p.1+p.2, p.1⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    omega
  · intro p hp q hq he
    have he₁ : p.1+p.2 = q.1+q.2 := congrArg Sigma.fst he
    have he₂ : p.1 = q.1 := congrArg Sigma.snd he
    cases p with
    | mk a b =>
      cases q with
      | mk c e =>
        dsimp at he₁ he₂
        have hb : b = e := by omega
        subst c
        subst e
        rfl
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    refine ⟨⟨p.2, p.1-p.2⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · apply Sigma.ext
      · dsimp
        omega
      · rfl
  · intro p hp
    change F p.1 p.2 = F p.1 (p.1+p.2-p.1)
    rw [Nat.add_sub_cancel_left]
end WP

namespace WP
lemma finite_kernel_inversion (m : ℕ) (k t u v : ℕ → ℝ)
    (hi : ∀ n ≤ m, ∑ j ∈ Finset.range (n+1), t j*k (n-j) = if n = 0 then 1 else 0)
    (he : ∀ l ≤ m, ∑ i ∈ Finset.range (m-l+1), k i*u (l+i) = v l) :
    u 0 = ∑ l ∈ Finset.range (m+1), t l*v l := by
  symm
  calc
    (∑ l ∈ Finset.range (m+1), t l*v l) =
        ∑ l ∈ Finset.range (m+1), ∑ i ∈ Finset.range (m-l+1), t l*(k i*u (l+i)) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [← he l (by have := Finset.mem_range.mp hl; omega), Finset.mul_sum]
    _ = ∑ j ∈ Finset.range (m+1), ∑ l ∈ Finset.range (j+1), t l*(k (j-l)*u (l+(j-l))) :=
      triangle_sum_reindex m _
    _ = ∑ j ∈ Finset.range (m+1),
        (∑ l ∈ Finset.range (j+1), t l*k (j-l))*u j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      have hl' : l ≤ j := by have := Finset.mem_range.mp hl; omega
      rw [Nat.add_sub_of_le hl']
      ring
    _ = ∑ j ∈ Finset.range (m+1), (if j = 0 then 1 else 0)*u j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hi j (by have := Finset.mem_range.mp hj; omega)]
    _ = u 0 := by simp
end WP
namespace WP
lemma sum_map_int (d : List ℕ) : (d.map Int.ofNat).sum = (d.sum : ℤ) := by
  induction d with
  | nil => simp
  | cons k d ih => simpa using congrArg (fun z : ℤ => (k : ℤ)+z) ih
lemma map_ofNat_toNat (d : List ℤ) (hd : ∀ k ∈ d, 0 ≤ k) :
    (d.map Int.toNat).map Int.ofNat = d := by
  induction d with
  | nil => rfl
  | cons k d ih =>
    simp only [List.map_cons]
    change (k.toNat : ℤ) :: (d.map Int.toNat).map Int.ofNat = k :: d
    rw [Int.toNat_of_nonneg (hd k (by simp)), ih (fun j hj => hd j (by simp [hj]))]
lemma signed_normalized_top (P : PsiTheory) (g : ℕ) (d : List ℤ) (Y : ℝ)
    (hY : Y ∈ Set.Icc 0 y₀) (hd : d.sum = 3*(g : ℤ)-3+d.length) :
    (if ∀ k ∈ d, 0 ≤ k then normalized P g (d.map Int.toNat) Y else 0) =
      weighted P.psi g d := by
  by_cases hn : ∀ k ∈ d, 0 ≤ k
  · rw [if_pos hn]
    by_cases hs : Stable g d.length
    · have hm := map_ofNat_toNat d hn
      have hdim : (d.map Int.toNat).sum = dimension g (d.map Int.toNat).length := by
        have he : (((d.map Int.toNat).sum : ℕ) : ℤ) = d.sum := by
          rw [← sum_map_int, hm]
        rw [hd] at he
        have hn3 : 3 ≤ 3*g+d.length := by unfold Stable at hs; omega
        have hg : ((dimension g d.length : ℕ) : ℤ) = 3*(g : ℤ)-3+d.length := by
          unfold dimension
          rw [Nat.cast_sub hn3]
          push_cast
          ring
        simp only [List.length_map]
        exact_mod_cast he.trans hg.symm
      rw [normalized_top P g _ Y hY hdim, hm]
    · have hv : P.psi g d = 0 := P.vanish g d (Or.inl hs)
      rw [normalized_unstable P g _ Y (by simpa using hs)]
      simp [weighted, hv]
  · rw [if_neg hn]
    have he : ∃ k ∈ d, k < 0 := by
      push_neg at hn
      exact hn
    have hv := P.vanish g d (Or.inr (Or.inl he))
    simp [weighted, hv]
end WP
namespace WP
lemma mem_backgrounds_iff (m : ℕ) (l : Fin m → ℕ) :
    l ∈ backgrounds m ↔ ∑ i : Fin m, (i.val+1)*l i = m := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hb (i : Fin m) : l i < m+1 := by
      have hi : (i.val+1)*l i ≤ ∑ j : Fin m, (j.val+1)*l j :=
        Finset.single_le_sum (f := fun j : Fin m => (j.val+1)*l j)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      have hh : l i ≤ (i.val+1)*l i := by nlinarith [Nat.zero_le i.val]
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨fun i => ⟨l i, hb i⟩, Finset.mem_univ _, rfl⟩, h⟩
lemma backgroundDegrees_length {m : ℕ} (l : Fin m → ℕ) :
    (backgroundDegrees l).length = ∑ i, l i := by
  simp [backgroundDegrees, List.finRange, List.sum_ofFn]
lemma backgroundDegrees_sum {m : ℕ} (l : Fin m → ℕ) :
    (backgroundDegrees l).sum = ∑ i, (i.val+2)*l i := by
  simp [backgroundDegrees, List.flatMap_def, List.sum_flatten, List.map_map,
    List.finRange, List.sum_ofFn, nsmul_eq_mul, mul_comm]
lemma background_dimension {m : ℕ} (l : Fin m → ℕ) (hl : l ∈ backgrounds m) :
    (backgroundDegrees l).sum = m+(backgroundDegrees l).length := by
  rw [backgroundDegrees_sum, backgroundDegrees_length]
  calc
    (∑ i, (i.val+2)*l i) = (∑ i, (i.val+1)*l i) + ∑ i, l i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = m+∑ i, l i := by rw [(mem_backgrounds_iff m l).mp hl]
lemma background_degree_compatible (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hd : d.sum ≤ dimension g d.length)
    (l : Fin (deficit g d) → ℕ) (hl : l ∈ backgrounds (deficit g d)) :
    (d ++ backgroundDegrees l).sum = dimension g (d ++ backgroundDegrees l).length := by
  have he := background_dimension l hl
  have hm : deficit g d+d.sum = dimension g d.length := Nat.sub_add_cancel hd
  have heq : dimension g (d.length+(backgroundDegrees l).length) =
      dimension g d.length+(backgroundDegrees l).length := by
    unfold dimension
    unfold Stable at hs
    omega
  simp only [List.sum_append, List.length_append]
  rw [heq, he]
  omega
end WP
namespace WP
lemma exponential_weight_split (t : ℝ) (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) * (t^n/(n.factorial : ℝ)) =
      (t^k/k.factorial) * (t^(n-k)/(n-k).factorial) := by
  have hb : (n.choose k : ℝ)*(k.factorial : ℝ)*((n-k).factorial : ℝ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hkn : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hnk : ((n-k).factorial : ℝ) ≠ 0 := by exact_mod_cast (n-k).factorial_ne_zero
  rw [show t^n = t^k*t^(n-k) by rw [← pow_add, Nat.add_sub_of_le hk]]
  field_simp
  linear_combination t^k*t^(n-k)*hb
lemma background_binomial_split {m : ℕ} (t : Fin m → ℝ) (l j : Fin m → ℕ)
    (hj : ∀ i, j i ≤ l i) :
    (∏ i, ((l i).choose (j i) : ℝ)) * (∏ i, t i^(l i)/(l i).factorial) =
      (∏ i, t i^(j i)/(j i).factorial) *
      (∏ i, t i^(l i-j i)/(l i-j i).factorial) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact exponential_weight_split (t i) (l i) (j i) (hj i)
end WP

namespace WP
lemma coeff_barK_interior (Y : ℝ) (hy : Y ≠ y₀) (n : ℕ) :
    coeff (barK Y) n =
      (r Y : ℂ)^n * iteratedDeriv (n+1) X Y / ((oddFactorial n : ℂ)*(a Y : ℂ)) := by
  have he : barK Y = fun w => K Y ((r Y : ℂ)*w)/(a Y : ℂ) := by
    funext w
    simp [barK, hy]
  unfold coeff
  rw [he, iteratedDeriv_div_const,
    iteratedDeriv_comp_const_mul (K_differentiable (Y : ℂ)).contDiff (r Y : ℂ),
    ]
  simp only [mul_zero]
  rw [iteratedDeriv_K_zero]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp
  <;> ring
lemma coeff_barK_critical (n : ℕ) :
    coeff (barK y₀) n = if n = 0 then 1 else if n = 1 then -1 else 0 := by
  have he : barK y₀ = fun w : ℂ => 1-w := by funext w; simp [barK]
  have ht : Analysis.taylor (barK y₀) = PowerSeries.C 1-PowerSeries.X := by
    rw [he, Analysis.taylor_sub (f := fun _ : ℂ => 1) (g := fun z : ℂ => z)
      analyticAt_const analyticAt_id, Analysis.taylor_const, Analysis.taylor_id]
  have hc := congrArg (PowerSeries.coeff n) ht
  simp only [Analysis.taylor_coeff, map_sub, PowerSeries.coeff_C, PowerSeries.coeff_X] at hc
  by_cases h0 : n = 0
  · subst n
    simpa using hc
  · by_cases h1 : n = 1 <;> simpa [h0, h1] using hc
lemma coeff_barK_interior_real (Y : ℝ) (hy : Y ≠ y₀) (n : ℕ) :
    coeff (barK Y) n = ((r Y^n*(iteratedDeriv (n+1) X Y).re/
      ((oddFactorial n : ℝ)*a Y) : ℝ) : ℂ) := by
  have hx : iteratedDeriv (n+1) X (Y : ℂ) =
      (((iteratedDeriv (n+1) X (Y : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using iteratedDeriv_X_im_ofReal (n+1) Y
  rw [coeff_barK_interior Y hy, hx]
  push_cast
  rfl
lemma barK_realCoefficients (Y : ℝ) : Analysis.RealCoefficients (barK Y) := by
  intro n
  by_cases hy : Y = y₀
  · subst Y
    rw [coeff_barK_critical]
    split_ifs <;> norm_num
  · rw [coeff_barK_interior_real Y hy]
    exact Complex.ofReal_im _
lemma realCoeff_barK_interior (Y : ℝ) (hy : Y ≠ y₀) (n : ℕ) :
    realCoeff (barK Y) n = r Y^n*(iteratedDeriv (n+1) X Y).re/
      ((oddFactorial n : ℝ)*a Y) := by
  unfold realCoeff
  rw [coeff_barK_interior_real Y hy, Complex.ofReal_re]
lemma barK_zero_closed (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) : barK Y 0 = 1 := by
  by_cases hy : Y = y₀
  · simp [barK, hy]
  · exact barK_zero Y ⟨hY.1, lt_of_le_of_ne hY.2 hy⟩
lemma theta_kernel_convolution (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (n : ℕ) :
    ∑ l ∈ Finset.range (n+1), theta Y l * realCoeff (barK Y) (n-l) =
      if n = 0 then 1 else 0 := by
  let p := Analysis.realTaylor (barK Y)
  have hp : PowerSeries.constantCoeff p ≠ 0 := by
    simp [p, realCoeff, coeff, barK_zero_closed Y hY]
  have hi : Analysis.realTaylor (fun z => (barK Y z)⁻¹) = p⁻¹ :=
    Analysis.realTaylor_inv ((barK_differentiable Y).analyticAt 0)
      (by rw [barK_zero_closed Y hY]; exact one_ne_zero) (barK_realCoefficients Y)
  have he := congrArg (PowerSeries.coeff n) (PowerSeries.inv_mul_cancel p hp)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
  rw [← hi] at he
  simpa only [Analysis.realTaylor_coeff, theta, p, map_one, PowerSeries.coeff_one] using he
end WP

namespace WP
lemma normalized_kernel_finite_inversion (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀)
    (m : ℕ) (u v : ℕ → ℝ)
    (he : ∀ l ≤ m, ∑ i ∈ Finset.range (m-l+1),
      realCoeff (barK Y) i*u (l+i) = v l) :
    u 0 = ∑ l ∈ Finset.range (m+1), theta Y l*v l :=
  finite_kernel_inversion m (realCoeff (barK Y)) (theta Y) u v
    (fun n _ => theta_kernel_convolution Y hY n) he
end WP
