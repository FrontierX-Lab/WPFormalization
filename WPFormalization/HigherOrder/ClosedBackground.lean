import WPFormalization.Intersection.CriticalBackground

/-! Exact finite background normalization on the full closed parameter interval.
The critical times are the canonical finite specialization (3,0,...), already
proved to give the original endpoint normalization. No continuity or limit is
assumed. The dimensional-support argument also gives the exact separating
Cauchy product at the critical parameter.
-/
noncomputable section
namespace WP
/-- The original interior background times with their exact critical specialization. -/
def closedBackgroundTime (N : ℕ) (Y : ℝ) (i : Fin (N+1)) : ℝ :=
  if Y = y₀ then if i.val = 0 then 3 else 0 else
    (-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y
lemma finiteBackgroundAmplitude_signed_normalized_closed (P : PsiTheory) (g : ℕ)
    (d : List ℤ) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (N B m : ℕ)
    (hN : m ≤ N+1) (hB : m ≤ B)
    (hdim : d.sum+(m : ℤ) = 3*(g : ℤ)-3+d.length) :
    finiteBackgroundAmplitude P g d B m (closedBackgroundTime N Y) =
      if ∀ k ∈ d, 0 ≤ k then normalized P g (d.map Int.toNat) Y else 0 := by
  change finiteBackgroundAmplitude P g d B m
    (fun i : Fin (N+1) => if Y = y₀ then if i.val = 0 then 3 else 0 else
      (-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y) = _
  by_cases hy : Y = y₀
  · subst Y
    simp only [ite_true]
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
        have hp := finiteBackgroundAmplitude_normalized_critical P g (d.map Int.toNat)
          (by simpa using hs) hd N B (by rw [hdef]; exact hB)
        rw [hm, hdef] at hp
        exact hp
      · rw [finiteBackgroundAmplitude_unstable P g d B m _ hs,
          normalized_unstable P g _ y₀ (by simpa using hs)]
    · rw [if_neg hn]
      have he : ∃ k ∈ d, k < 0 := by push Not at hn; exact hn
      exact finiteBackgroundAmplitude_negative P g d B m _ he
  · have hi : Y ∈ Set.Ico 0 y₀ := ⟨hY.1, lt_of_le_of_ne hY.2 hy⟩
    simpa only [closedBackgroundTime, if_neg hy] using
      finiteBackgroundAmplitude_signed_normalized P g d Y hi (N+1) B m hN hB hdim

lemma finiteBackgroundAmplitude_convolution_support_closed (P : PsiTheory) (g₁ g₂ : ℕ)
    (d₁ d₂ : List ℤ) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (N B m : ℕ)
    (hN : m ≤ N+1) (hB : m ≤ B)
    (htotal : d₁.sum+d₂.sum+(m : ℤ) =
      (3*(g₁ : ℤ)-3+d₁.length)+(3*(g₂ : ℤ)-3+d₂.length)) :
    (∑ k ∈ Finset.range (m+1),
      finiteBackgroundAmplitude P g₁ d₁ B k
        (closedBackgroundTime N Y)*
      finiteBackgroundAmplitude P g₂ d₂ B (m-k)
        (closedBackgroundTime N Y)) =
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
              (closedBackgroundTime N Y)*
            finiteBackgroundAmplitude P g₂ d₂ B (m-k)
              (closedBackgroundTime N Y) := by
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
          rw [finiteBackgroundAmplitude_signed_normalized_closed P g₁ d₁ Y hY N B k
              (by omega) (by omega) hdim₁,
            finiteBackgroundAmplitude_signed_normalized_closed P g₂ d₂ Y hY N B (m-k)
              (by omega) (by omega) hdim₂]
end WP
