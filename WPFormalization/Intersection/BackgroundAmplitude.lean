import WPFormalization.Intersection.BackgroundConvolution
/-! Fixed-coordinate finite background amplitudes, their exact dimensional
support, and their identification with the original normalized interior
amplitudes. This is a reformulation of the given finite sum, not a new model. -/
noncomputable section
namespace WP
/-- The finite exponential background amplitude on a fixed ambient coordinate range. -/
def finiteBackgroundAmplitude (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (B m : ℕ) (t : Fin N → ℝ) : ℝ :=
  doubleWeight d * ∑ l ∈ backgroundVectors N B m,
    P.psi g (d ++ (backgroundDegrees l).map Int.ofNat) *
      ∏ i : Fin N, t i^(l i)/(l i).factorial
lemma background_dimension_general {N : ℕ} (l : Fin N → ℕ) :
    (backgroundDegrees l).sum = backgroundDegree l+(backgroundDegrees l).length := by
  rw [backgroundDegrees_sum, backgroundDegrees_length]
  unfold backgroundDegree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring
lemma finiteBackgroundAmplitude_negative (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (B m : ℕ) (t : Fin N → ℝ) (hd : ∃ k ∈ d, k < 0) :
    finiteBackgroundAmplitude P g d B m t = 0 := by
  unfold finiteBackgroundAmplitude
  suffices he : (∑ l ∈ backgroundVectors N B m,
      P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)*
        ∏ i : Fin N, t i^(l i)/(l i).factorial) = 0 by rw [he, mul_zero]
  apply Finset.sum_eq_zero
  intro l hl
  have hv : P.psi g (d ++ (backgroundDegrees l).map Int.ofNat) = 0 := by
    apply P.vanish
    apply Or.inr
    apply Or.inl
    obtain ⟨k, hk, hneg⟩ := hd
    exact ⟨k, List.mem_append_left _ hk, hneg⟩
  rw [hv, zero_mul]
lemma finiteBackgroundAmplitude_dimension (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (B m : ℕ) (t : Fin N → ℝ)
    (hd : d.sum+(m : ℤ) ≠ 3*(g : ℤ)-3+d.length) :
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
    apply P.vanish
    apply Or.inr
    apply Or.inr
    simp only [List.sum_append, List.length_append, List.length_map, Nat.cast_add]
    intro he
    apply hd
    omega
  rw [hv, zero_mul]
lemma finiteBackgroundAmplitude_normalized_interior (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) (hs : Stable g d.length)
    (hd : d.sum ≤ dimension g d.length) (s B : ℕ) (hB : deficit g d ≤ B) :
    finiteBackgroundAmplitude P g (d.map Int.ofNat) B (deficit g d)
      (fun i : Fin (deficit g d+s) =>
        (-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y) =
      normalized P g d Y := by
  rw [normalized_background_sum_interior P g d Y hY, if_pos ⟨hs, hd⟩]
  unfold finiteBackgroundAmplitude
  have hw : doubleWeight (d.map Int.ofNat) =
      (d.map (fun k => (oddFactorial k : ℝ))).prod := by
    simp [doubleWeight, List.map_map, Function.comp_def]
  rw [hw, sum_backgroundVectors_zeroExtend (deficit g d) s B hB]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [backgroundDegrees_zeroExtend, background_weight_zeroExtend]
  simp only [pure, List.map_append, Fin.val_castAdd]
end WP
