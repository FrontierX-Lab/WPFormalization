import WPFormalization.Intersection.BackgroundAmplitude
import WPFormalization.Intersection.TopDegree
/-! Exact support and signed normalization of finite background amplitudes.
The separating Cauchy product is reduced to the unique compatible pair of
component dimensions, with all unstable and negative states retained as zero. -/
noncomputable section
namespace WP
lemma background_length_le_degree {N : ℕ} (l : Fin N → ℕ) :
    (backgroundDegrees l).length ≤ backgroundDegree l := by
  rw [backgroundDegrees_length]
  unfold backgroundDegree
  apply Finset.sum_le_sum
  intro i hi
  nlinarith [Nat.zero_le i.val]
lemma finiteBackgroundAmplitude_unstable_of_nonneg (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (B m : ℕ) (t : Fin N → ℝ)
    (hd : ∀ k ∈ d, 0 ≤ k) (hs : ¬Stable g d.length) :
    finiteBackgroundAmplitude P g d B m t = 0 := by
  unfold finiteBackgroundAmplitude
  suffices he : (∑ l ∈ backgroundVectors N B m,
      P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)*
        ∏ i : Fin N, t i^(l i)/(l i).factorial) = 0 by rw [he, mul_zero]
  apply Finset.sum_eq_zero
  intro l hl
  have hdeg : backgroundDegree l = m := (Finset.mem_filter.mp hl).2
  have hbg : ((backgroundDegrees l).map Int.ofNat).sum =
      (m : ℤ)+(backgroundDegrees l).length := by
    rw [sum_map_int]
    have he := background_dimension_general l
    rw [hdeg] at he
    exact_mod_cast he
  have hv : P.psi g (d ++ (backgroundDegrees l).map Int.ofNat) = 0 := by
    by_cases hdim : (d ++ (backgroundDegrees l).map Int.ofNat).sum =
        3*(g : ℤ)-3+(d ++ (backgroundDegrees l).map Int.ofNat).length
    · have hds : 0 ≤ d.sum := List.sum_nonneg hd
      have hraw : d.sum+(m : ℤ) = 3*(g : ℤ)-3+d.length := by
        simp only [List.sum_append, List.length_append, List.length_map, Nat.cast_add] at hdim
        omega
      have hm : m = 0 := by unfold Stable at hs; omega
      have hlen : (backgroundDegrees l).length = 0 := by
        have hh := background_length_le_degree l
        omega
      apply P.vanish
      apply Or.inl
      simpa only [List.length_append, List.length_map, hlen, Nat.add_zero] using hs
    · exact P.vanish g _ (Or.inr (Or.inr hdim))
  rw [hv, zero_mul]
lemma finiteBackgroundAmplitude_excess (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (B m : ℕ) (t : Fin N → ℝ)
    (hd : 3*(g : ℤ)-3+d.length < d.sum) :
    finiteBackgroundAmplitude P g d B m t = 0 :=
  finiteBackgroundAmplitude_dimension P g d B m t (by omega)
lemma finiteBackgroundAmplitude_normalized_interior_of_le (P : PsiTheory) (g : ℕ)
    (d : List ℕ) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) (hs : Stable g d.length)
    (hd : d.sum ≤ dimension g d.length) (N B : ℕ)
    (hN : deficit g d ≤ N) (hB : deficit g d ≤ B) :
    finiteBackgroundAmplitude P g (d.map Int.ofNat) B (deficit g d)
      (fun i : Fin N => (-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y) =
      normalized P g d Y := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hN
  exact finiteBackgroundAmplitude_normalized_interior P g d Y hY hs hd s B hB
end WP
namespace WP
lemma finiteBackgroundAmplitude_unstable (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (B m : ℕ) (t : Fin N → ℝ) (hs : ¬Stable g d.length) :
    finiteBackgroundAmplitude P g d B m t = 0 := by
  by_cases hd : ∀ k ∈ d, 0 ≤ k
  · exact finiteBackgroundAmplitude_unstable_of_nonneg P g d B m t hd hs
  · have he : ∃ k ∈ d, k < 0 := by
      push Not at hd
      exact hd
    exact finiteBackgroundAmplitude_negative P g d B m t he
lemma finiteBackgroundAmplitude_signed_normalized (P : PsiTheory) (g : ℕ)
    (d : List ℤ) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) (N B m : ℕ)
    (hN : m ≤ N) (hB : m ≤ B)
    (hdim : d.sum+(m : ℤ) = 3*(g : ℤ)-3+d.length) :
    finiteBackgroundAmplitude P g d B m
      (fun i : Fin N => (-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y) =
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
      have hproof := finiteBackgroundAmplitude_normalized_interior_of_le P g
        (d.map Int.toNat) Y hY (by simpa using hs) hd N B
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
lemma finiteBackgroundAmplitude_convolution_support (P : PsiTheory) (g₁ g₂ : ℕ)
    (d₁ d₂ : List ℤ) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) (N B m : ℕ)
    (hN : m ≤ N) (hB : m ≤ B)
    (htotal : d₁.sum+d₂.sum+(m : ℤ) =
      (3*(g₁ : ℤ)-3+d₁.length)+(3*(g₂ : ℤ)-3+d₂.length)) :
    (∑ k ∈ Finset.range (m+1),
      finiteBackgroundAmplitude P g₁ d₁ B k
        (fun i : Fin N => (-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y)*
      finiteBackgroundAmplitude P g₂ d₂ B (m-k)
        (fun i : Fin N => (-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y)) =
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
              (fun i : Fin N => (-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y)*
            finiteBackgroundAmplitude P g₂ d₂ B (m-k)
              (fun i : Fin N => (-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y) := by
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
          rw [finiteBackgroundAmplitude_signed_normalized P g₁ d₁ Y hY N B k
              (by omega) (by omega) hdim₁,
            finiteBackgroundAmplitude_signed_normalized P g₂ d₂ Y hY N B (m-k)
              (by omega) (by omega) hdim₂]
end WP
