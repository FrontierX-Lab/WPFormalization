import WPFormalization.Weighted.PackProfile

/-! The complete actual weighted separating-mass estimate, before the uniform mass-to-square-root bound. -/
noncomputable section
namespace WP
lemma weightedSeparating_mass_bound (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ, 0<C ∧ ∀ g pivot : ℕ, ∀ d : List ℕ, 2≤g →
      (pivot::d).sum≤dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
      weightedSeparating c Y g pivot d≤
        C*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot::d))*
          (1+inactive (pivot::d))/Real.rpow (complexity g (d.length+1)) (3/2 : ℝ) := by
  obtain ⟨C,hC,hpack⟩ := separatingPack_profile c hc
  obtain ⟨G,hG,hGamma⟩ := actual_partitionGamma_total
  refine ⟨C*G/3,by positivity,?_⟩
  intro g pivot d hg hd Y hY
  let h := complexity g (d.length+1)
  let m := deficit g (pivot::d)
  have hh : 2≤h := by dsimp only [h]; unfold complexity; omega
  have hQ (l : ℕ) : 0≤linearQ Y h m l := linearQ_nonneg Y hY h m l hh
  have hGS : (∑ iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range d.length).powerset,
      partitionGammaTerm (inactiveIndices d) g d.length iU.1 iU.2) ≤
      G*(1+(inactive d : ℝ))/Real.rpow h (3/2 : ℝ) := by
    rw [Finset.sum_product]
    exact hGamma g pivot d hg hd
  have hlayer (l : ℕ) (hl : l ∈ Finset.range (m+1)) :
      (∑ iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range d.length).powerset,
        if separatingOrientation g d.length iU then separatingPack c Y g pivot d l iU else 0) ≤
      (C*G/6)*linearQ Y h m l*(1+(inactive d : ℝ))/Real.rpow h (3/2 : ℝ) := by
    have hl' : l≤deficit g (pivot::d) := by have := Finset.mem_range.mp hl; omega
    calc
      _ ≤ ∑ iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range d.length).powerset,
          (C/6*linearQ Y h m l)*partitionGammaTerm (inactiveIndices d) g d.length iU.1 iU.2 := by
        apply Finset.sum_le_sum
        intro iU hiU
        have hi := Finset.mem_range.mp (Finset.mem_product.mp hiU).1
        have hI := Finset.mem_powerset.mp (Finset.mem_product.mp hiU).2
        by_cases hsmall : separatingOrientation g d.length iU
        · rw [if_pos hsmall]
          exact hpack g pivot d hg hd Y hY l hl' iU.1 (by omega) iU.2 hI hsmall
        · rw [if_neg hsmall]
          have hΓzero : partitionGammaTerm (inactiveIndices d) g d.length iU.1 iU.2=0 := by
            unfold partitionGammaTerm
            dsimp only
            apply if_neg
            intro hv
            exact hsmall hv.2.2.1
          rw [hΓzero,mul_zero]
      _ = (C/6*linearQ Y h m l)*
          (∑ iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range d.length).powerset,
            partitionGammaTerm (inactiveIndices d) g d.length iU.1 iU.2) := (Finset.mul_sum _ _ _).symm
      _ ≤ (C/6*linearQ Y h m l)*(G*(1+(inactive d : ℝ))/Real.rpow h (3/2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hGS (mul_nonneg (div_nonneg hC.le (by norm_num)) (hQ l))
      _ = _ := by ring
  have hsum : (∑ l ∈ Finset.range (m+1),
      (C*G/6)*linearQ Y h m l*(1+(inactive d : ℝ))/Real.rpow h (3/2 : ℝ)) =
      (C*G/6)*linearS₀ Y h m*(1+(inactive d : ℝ))/Real.rpow h (3/2 : ℝ) := by
    calc
      _ = ∑ l ∈ Finset.range (m+1), ((C*G/6)*(1+(inactive d : ℝ))/Real.rpow h (3/2 : ℝ))*linearQ Y h m l := by
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = ((C*G/6)*(1+(inactive d : ℝ))/Real.rpow h (3/2 : ℝ))*
          (∑ l ∈ Finset.range (m+1), linearQ Y h m l) := (Finset.mul_sum _ _ _).symm
      _ = _ := by unfold linearS₀; ring
  calc
    _ ≤ 2*(∑ l ∈ Finset.range (m+1),
        ∑ iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range d.length).powerset,
          if separatingOrientation g d.length iU then separatingPack c Y g pivot d l iU else 0) :=
      weightedSeparating_orientation c Y g pivot d hg hY
    _ ≤ 2*(∑ l ∈ Finset.range (m+1),
        (C*G/6)*linearQ Y h m l*(1+(inactive d : ℝ))/Real.rpow h (3/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlayer) (by norm_num)
    _ = (C*G/3)*linearS₀ Y h m*(1+(inactive d : ℝ))/Real.rpow h (3/2 : ℝ) := by rw [hsum]; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg h) _)
      have hi : (inactive d : ℝ) ≤ inactive (pivot::d) := by exact_mod_cast (inactive_cons_bounds pivot d).1
      exact mul_le_mul_of_nonneg_left (by linarith : 1+(inactive d : ℝ)≤1+inactive (pivot::d))
        (mul_nonneg (by positivity) (linearS₀_nonneg Y hY h m hh))
end WP
