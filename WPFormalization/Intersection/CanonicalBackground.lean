import WPFormalization.Intersection.CriticalBackground
import WPFormalization.Intersection.BackgroundDVV
/-! The canonical normalized background times are defined from the actual
`barK` coefficients. This proves their interior and critical formulas, identifies
all signed amplitudes on the closed parameter interval, and converts the full
finite-background child operator to the original normalized child amplitudes. -/
noncomputable section
namespace WP
/-- The normalized background times are fixed by the genuine kernel coefficients. -/
def normalizedBackgroundTime (Y : ℝ) (i : ℕ) : ℝ :=
  -(oddFactorial (i+1) : ℝ)*realCoeff (barK Y) (i+1)
lemma realCoeff_barK_succ_time (Y : ℝ) (i : ℕ) :
    realCoeff (barK Y) (i+1) = -normalizedBackgroundTime Y i/(oddFactorial (i+1) : ℝ) := by
  unfold normalizedBackgroundTime
  have ho : (oddFactorial (i+1) : ℝ) ≠ 0 := by exact_mod_cast (oddFactorial_pos (i+1)).ne'
  field_simp
lemma normalizedBackgroundTime_interior (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) (i : ℕ) :
    normalizedBackgroundTime Y i =
      (-(iteratedDeriv (i+2) X Y).re)*r Y^(i+1)/a Y := by
  unfold normalizedBackgroundTime
  rw [realCoeff_barK_interior Y (ne_of_lt hY.2)]
  rw [show i+1+1 = i+2 by omega]
  have ho : (oddFactorial (i+1) : ℝ) ≠ 0 := by exact_mod_cast (oddFactorial_pos (i+1)).ne'
  have ha := a_ne_zero Y hY
  field_simp
  <;> ring
lemma normalizedBackgroundTime_critical (i : ℕ) :
    normalizedBackgroundTime y₀ i = if i = 0 then 3 else 0 := by
  unfold normalizedBackgroundTime realCoeff
  rw [coeff_barK_critical]
  by_cases hi : i = 0
  · subst i
    norm_num [oddFactorial, Finset.prod_range_succ]
  · have hzero : i+1 ≠ 0 := by omega
    have hone : i+1 ≠ 1 := by omega
    simp [hi, hzero, hone]
lemma finiteBackgroundAmplitude_normalized_canonical (P : PsiTheory) (g : ℕ)
    (d : List ℕ) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (hs : Stable g d.length)
    (hd : d.sum ≤ dimension g d.length) (N B : ℕ) (hNp : 0 < N)
    (hN : deficit g d ≤ N) (hB : deficit g d ≤ B) :
    finiteBackgroundAmplitude P g (d.map Int.ofNat) B (deficit g d)
      (fun i : Fin N => normalizedBackgroundTime Y i.val) = normalized P g d Y := by
  by_cases hy : Y = y₀
  · subst Y
    cases N with
    | zero => omega
    | succ N =>
      have ht : (fun i : Fin (N+1) => normalizedBackgroundTime y₀ i.val) =
          fun i : Fin (N+1) => if i.val = 0 then 3 else 0 := by
        funext i
        exact normalizedBackgroundTime_critical i.val
      rw [ht]
      exact finiteBackgroundAmplitude_normalized_critical P g d hs hd N B hB
  · have hi : Y ∈ Set.Ico 0 y₀ := ⟨hY.1, lt_of_le_of_ne hY.2 hy⟩
    have ht : (fun i : Fin N => normalizedBackgroundTime Y i.val) =
        fun i : Fin N => (-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y := by
      funext i
      exact normalizedBackgroundTime_interior Y hi i.val
    rw [ht]
    exact finiteBackgroundAmplitude_normalized_interior_of_le P g d Y hi hs hd N B hN hB
end WP

namespace WP
lemma finiteBackgroundAmplitude_signed_normalized_canonical (P : PsiTheory) (g : ℕ)
    (d : List ℤ) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (N B m : ℕ)
    (hNp : 0 < N) (hN : m ≤ N) (hB : m ≤ B)
    (hdim : d.sum+(m : ℤ) = 3*(g : ℤ)-3+d.length) :
    finiteBackgroundAmplitude P g d B m
      (fun i : Fin N => normalizedBackgroundTime Y i.val) =
      if ∀ k ∈ d, 0 ≤ k then normalized P g (d.map Int.toNat) Y else 0 := by
  by_cases hn : ∀ k ∈ d, 0 ≤ k
  · rw [if_pos hn]
    by_cases hs : Stable g d.length
    · have hm := map_ofNat_toNat d hn
      have he : (((d.map Int.toNat).sum : ℕ) : ℤ) = d.sum := by
        rw [← sum_map_int, hm]
      have hc := dimension_cast_of_stable g d.length hs
      have hsum : (d.map Int.toNat).sum+m = dimension g (d.map Int.toNat).length := by
        simp only [List.length_map]
        exact_mod_cast (by omega : (((d.map Int.toNat).sum : ℕ) : ℤ)+(m : ℤ) =
          ((dimension g d.length : ℕ) : ℤ))
      have hd : (d.map Int.toNat).sum ≤ dimension g (d.map Int.toNat).length := by omega
      have hdef : deficit g (d.map Int.toNat) = m := by unfold deficit; omega
      have hproof := finiteBackgroundAmplitude_normalized_canonical P g
        (d.map Int.toNat) Y hY (by simpa using hs) hd N B hNp
        (by rw [hdef]; exact hN) (by rw [hdef]; exact hB)
      rw [hm, hdef] at hproof
      exact hproof
    · rw [finiteBackgroundAmplitude_unstable P g d B m _ hs,
        normalized_unstable P g _ Y (by simpa using hs)]
  · rw [if_neg hn]
    have he : ∃ k ∈ d, k < 0 := by
      push Not at hn
      exact hn
    exact finiteBackgroundAmplitude_negative P g d B m _ he
end WP
namespace WP
lemma finiteBackgroundAmplitude_convolution_support_canonical (P : PsiTheory) (g₁ g₂ : ℕ)
    (d₁ d₂ : List ℤ) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (N B m : ℕ)
    (hNp : 0 < N) (hN : m ≤ N) (hB : m ≤ B)
    (htotal : d₁.sum+d₂.sum+(m : ℤ) =
      (3*(g₁ : ℤ)-3+d₁.length)+(3*(g₂ : ℤ)-3+d₂.length)) :
    (∑ k ∈ Finset.range (m+1),
      finiteBackgroundAmplitude P g₁ d₁ B k
        (fun i : Fin N => normalizedBackgroundTime Y i.val)*
      finiteBackgroundAmplitude P g₂ d₂ B (m-k)
        (fun i : Fin N => normalizedBackgroundTime Y i.val)) =
    (if ∀ k ∈ d₁, 0 ≤ k then normalized P g₁ (d₁.map Int.toNat) Y else 0)*
      (if ∀ k ∈ d₂, 0 ≤ k then normalized P g₂ (d₂.map Int.toNat) Y else 0) := by
  let D : ℤ := 3*(g₁ : ℤ)-3+d₁.length-d₁.sum
  by_cases hlo : D < 0
  · have hex : 3*(g₁ : ℤ)-3+d₁.length < d₁.sum := by dsimp [D] at hlo; omega
    rw [signed_normalized_excess P g₁ d₁ Y hex, zero_mul]
    apply Finset.sum_eq_zero
    intro k hk
    rw [finiteBackgroundAmplitude_excess P g₁ d₁ B k _ hex, zero_mul]
  · by_cases hhi : (m : ℤ) < D
    · have hex : 3*(g₂ : ℤ)-3+d₂.length < d₂.sum := by dsimp [D] at hhi; omega
      rw [signed_normalized_excess P g₂ d₂ Y hex, mul_zero]
      apply Finset.sum_eq_zero
      intro k hk
      rw [finiteBackgroundAmplitude_excess P g₂ d₂ B (m-k) _ hex, mul_zero]
    · have hD : 0 ≤ D := by omega
      let k := D.toNat
      have hkD : (k : ℤ) = D := Int.toNat_of_nonneg hD
      have hkm : k ≤ m := by exact_mod_cast (by omega : (k : ℤ) ≤ (m : ℤ))
      have hdim₁ : d₁.sum+(k : ℤ) = 3*(g₁ : ℤ)-3+d₁.length := by dsimp [D] at hkD; omega
      have hdim₂ : d₂.sum+((m-k : ℕ) : ℤ) = 3*(g₂ : ℤ)-3+d₂.length := by
        rw [Nat.cast_sub hkm]
        omega
      calc
        _ = finiteBackgroundAmplitude P g₁ d₁ B k
              (fun i : Fin N => normalizedBackgroundTime Y i.val)*
            finiteBackgroundAmplitude P g₂ d₂ B (m-k)
              (fun i : Fin N => normalizedBackgroundTime Y i.val) := by
          apply Finset.sum_eq_single k
          · intro j hj hjk
            have hwrong : d₁.sum+(j : ℤ) ≠ 3*(g₁ : ℤ)-3+d₁.length := by
              intro he
              have hjeq : (j : ℤ) = (k : ℤ) := by omega
              exact hjk (by exact_mod_cast hjeq)
            rw [finiteBackgroundAmplitude_dimension P g₁ d₁ B j _ hwrong, zero_mul]
          · intro hk
            exact False.elim (hk (Finset.mem_range.mpr (Nat.lt_succ_of_le hkm)))
        _ = _ := by
          rw [finiteBackgroundAmplitude_signed_normalized_canonical P g₁ d₁ Y hY N B k hNp
              (by omega) (by omega) hdim₁,
            finiteBackgroundAmplitude_signed_normalized_canonical P g₂ d₂ Y hY N B (m-k) hNp
              (by omega) (by omega) hdim₂]
end WP
namespace WP
def normalizedChildren (P : PsiTheory) (g p : ℕ) (d : List ℤ) (Y : ℝ) : ℝ :=
  (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*
    (if ∀ k ∈ (((p : ℤ)+d[j]!-1) :: d.eraseIdx j), 0 ≤ k then
      normalized P g ((((p : ℤ)+d[j]!-1) :: d.eraseIdx j).map Int.toNat) Y else 0)) +
  (if g = 0 then 0 else (1/2 : ℝ)*∑ u ∈ Finset.range (p-1),
    if ∀ k ∈ ((u : ℤ) :: ((p : ℤ)-2-u) :: d), 0 ≤ k then
      normalized P (g-1) (((u : ℤ) :: ((p : ℤ)-2-u) :: d).map Int.toNat) Y else 0) +
  (1/2 : ℝ)*∑ u ∈ Finset.range (p-1), ∑ g₁ ∈ Finset.range (g+1),
    ∑ I ∈ (Finset.range d.length).powerset,
      (if ∀ k ∈ ((u : ℤ) :: selected d I), 0 ≤ k then
        normalized P g₁ (((u : ℤ) :: selected d I).map Int.toNat) Y else 0)*
      (if ∀ k ∈ (((p : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)), 0 ≤ k then
        normalized P (g-g₁) ((((p : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)).map Int.toNat) Y else 0)
lemma finiteBackgroundChildren_normalized (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (N B k : ℕ) (hNp : 0 < N)
    (hN : k ≤ N) (hB : k ≤ B)
    (hdim : ((p : ℤ) :: d).sum+(k : ℤ) = 3*(g : ℤ)-3+((p : ℤ) :: d).length) :
    finiteBackgroundChildren P g p d B k (fun i : Fin N => normalizedBackgroundTime Y i.val) =
      normalizedChildren P g p d Y := by
  have htop : (((p : ℤ)+(k : ℤ)) :: d).sum =
      3*(g : ℤ)-3+(((p : ℤ)+(k : ℤ)) :: d).length := by
    simp only [List.sum_cons, List.length_cons] at hdim ⊢
    omega
  unfold finiteBackgroundChildren normalizedChildren
  apply congrArg₂ (fun a b : ℝ => a+b)
  · apply congrArg₂ (fun a b : ℝ => a+b)
    · apply Finset.sum_congr rfl
      intro j hj
      congr 1
      apply finiteBackgroundAmplitude_signed_normalized_canonical P g _ Y hY N B k hNp hN hB
      have he := merger_dimension g ((p : ℤ)+(k : ℤ)) d htop j (Finset.mem_range.mp hj)
      simp only [List.sum_cons, List.length_cons] at he ⊢
      omega
    · by_cases hg : g = 0
      · simp [hg]
      · simp only [hg, ite_false]
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        apply finiteBackgroundAmplitude_signed_normalized_canonical P (g-1) _ Y hY N B k hNp hN hB
        have he := contraction_dimension g hg ((p : ℤ)+(k : ℤ)) d htop u
        simp only [List.sum_cons, List.length_cons] at he ⊢
        omega
  · congr 1
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro g₁ hg₁
    apply Finset.sum_congr rfl
    intro I hI
    apply finiteBackgroundAmplitude_convolution_support_canonical P g₁ (g-g₁) _ _ Y hY N B k hNp hN hB
    have hgg : g₁ ≤ g := by have := Finset.mem_range.mp hg₁; omega
    have he := separating_dimension g g₁ hgg ((p : ℤ)+(k : ℤ)) d htop u I
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at he ⊢
    omega
end WP
