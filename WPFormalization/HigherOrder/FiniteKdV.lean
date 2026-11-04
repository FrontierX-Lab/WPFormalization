import WPFormalization.HigherOrder.ClosedBackground

/-! Finite descendant-tail splitting into zero markings and exponential backgrounds.
The ordered subset sum becomes an actual binomial factor and the finite Cauchy
product of component amplitudes. These are finite identities for arbitrary
background times and do not assume KdV or any asymptotic statement.
-/
noncomputable section
namespace WP
lemma zero_background_selected_split (P : PsiTheory) (g₁ g₂ n : ℕ)
    {N : ℕ} (l : Fin N → ℕ) :
    (∑ I ∈ (Finset.range ((List.replicate n (0 : ℤ)) ++
        (backgroundDegrees l).map Int.ofNat).length).powerset,
      P.psi g₁ (List.replicate 2 0 ++ selected (List.replicate n 0 ++ (backgroundDegrees l).map Int.ofNat) I)*
      P.psi g₂ (List.replicate 2 0 ++ selected (List.replicate n 0 ++ (backgroundDegrees l).map Int.ofNat)
        ((Finset.range (List.replicate n 0 ++ (backgroundDegrees l).map Int.ofNat).length) \ I))) =
    ∑ s ∈ Finset.range (n+1), (n.choose s : ℝ)*
      ∑ j ∈ subBackgrounds l, (∏ i, ((l i).choose (j i) : ℝ))*
        P.psi g₁ (List.replicate (s+2) 0 ++ (backgroundDegrees j).map Int.ofNat)*
        P.psi g₂ (List.replicate (n-s+2) 0 ++ (backgroundDegrees (fun i => l i-j i)).map Int.ofNat) := by
  rw [sum_selected_append (List.replicate n 0) ((backgroundDegrees l).map Int.ofNat)
    (fun x y => P.psi g₁ (List.replicate 2 0 ++ x)*P.psi g₂ (List.replicate 2 0 ++ y))]
  have hinner (I : Finset ℕ) :
      (∑ J ∈ (Finset.range ((backgroundDegrees l).map Int.ofNat).length).powerset,
        P.psi g₁ (List.replicate 2 0 ++ (selected (List.replicate n 0) I ++ selected ((backgroundDegrees l).map Int.ofNat) J))*
        P.psi g₂ (List.replicate 2 0 ++ (selected (List.replicate n 0) ((Finset.range n) \ I) ++
          selected ((backgroundDegrees l).map Int.ofNat) ((Finset.range ((backgroundDegrees l).map Int.ofNat).length) \ J)))) =
      ∑ j ∈ subBackgrounds l, (∏ i, ((l i).choose (j i) : ℝ))*
        P.psi g₁ (List.replicate 2 0 ++ (selected (List.replicate n 0) I ++ (backgroundDegrees j).map Int.ofNat))*
        P.psi g₂ (List.replicate 2 0 ++ (selected (List.replicate n 0) ((Finset.range n) \ I) ++
          (backgroundDegrees (fun i => l i-j i)).map Int.ofNat)) := by
    simpa only [List.length_map,mul_assoc] using sum_selected_background l
      (fun x y => P.psi g₁ (List.replicate 2 0 ++ (selected (List.replicate n 0) I ++ x))*
        P.psi g₂ (List.replicate 2 0 ++ (selected (List.replicate n 0) ((Finset.range n) \ I) ++ y)))
  simp only [List.length_replicate] at *
  simp_rw [hinner]
  rw [sum_selected_replicate n 0 (fun x y =>
    ∑ j ∈ subBackgrounds l, (∏ i, ((l i).choose (j i) : ℝ))*
      P.psi g₁ (List.replicate 2 0 ++ (x ++ (backgroundDegrees j).map Int.ofNat))*
      P.psi g₂ (List.replicate 2 0 ++ (y ++ (backgroundDegrees (fun i => l i-j i)).map Int.ofNat)))]
  simp only [← List.append_assoc, ← List.replicate_add, Nat.add_comm 2]

lemma finiteBackgroundAmplitude_zeros (P : PsiTheory) (g p : ℕ) {N : ℕ}
    (B m : ℕ) (t : Fin N → ℝ) :
    finiteBackgroundAmplitude P g (List.replicate p 0) B m t =
      ∑ l ∈ backgroundVectors N B m,
        (∏ i, t i^(l i)/(l i).factorial)*
          P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat) := by
  have ho : oddFactorial 0 = 1 := by norm_num [oddFactorial]
  unfold finiteBackgroundAmplitude doubleWeight
  simp only [List.map_replicate, Int.toNat_zero, ho, Nat.cast_one, List.prod_replicate, one_pow, one_mul]
  apply Finset.sum_congr rfl
  intro l hl
  ring

lemma finite_background_zero_split (P : PsiTheory) (g₁ g₂ n : ℕ)
    {N B M : ℕ} (hM : M ≤ B) (t : Fin N → ℝ) :
    (∑ l ∈ backgroundVectors N B M, (∏ i, t i^(l i)/(l i).factorial)*
      ∑ I ∈ (Finset.range ((List.replicate n (0 : ℤ)) ++ (backgroundDegrees l).map Int.ofNat).length).powerset,
        P.psi g₁ (List.replicate 2 0 ++ selected (List.replicate n 0 ++ (backgroundDegrees l).map Int.ofNat) I)*
        P.psi g₂ (List.replicate 2 0 ++ selected (List.replicate n 0 ++ (backgroundDegrees l).map Int.ofNat)
          ((Finset.range (List.replicate n 0 ++ (backgroundDegrees l).map Int.ofNat).length) \ I))) =
    ∑ s ∈ Finset.range (n+1), (n.choose s : ℝ)*
      ∑ k ∈ Finset.range (M+1),
        finiteBackgroundAmplitude P g₁ (List.replicate (s+2) 0) B k t *
          finiteBackgroundAmplitude P g₂ (List.replicate (n-s+2) 0) B (M-k) t := by
  simp_rw [zero_background_selected_split P g₁ g₂ n]
  calc
    _ = ∑ l ∈ backgroundVectors N B M, ∑ s ∈ Finset.range (n+1),
        (n.choose s : ℝ)*((∏ i, t i^(l i)/(l i).factorial)*
          ∑ j ∈ subBackgrounds l, (∏ i, ((l i).choose (j i) : ℝ))*
            P.psi g₁ (List.replicate (s+2) 0 ++ (backgroundDegrees j).map Int.ofNat)*
            P.psi g₂ (List.replicate (n-s+2) 0 ++ (backgroundDegrees (fun i => l i-j i)).map Int.ofNat)) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = ∑ s ∈ Finset.range (n+1), (n.choose s : ℝ)*
        (∑ l ∈ backgroundVectors N B M, (∏ i, t i^(l i)/(l i).factorial)*
          ∑ j ∈ subBackgrounds l, (∏ i, ((l i).choose (j i) : ℝ))*
            P.psi g₁ (List.replicate (s+2) 0 ++ (backgroundDegrees j).map Int.ofNat)*
            P.psi g₂ (List.replicate (n-s+2) 0 ++ (backgroundDegrees (fun i => l i-j i)).map Int.ofNat)) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      congr 1
      rw [background_exponential_convolution hM t
        (fun l => P.psi g₁ (List.replicate (s+2) 0 ++ (backgroundDegrees l).map Int.ofNat))
        (fun l => P.psi g₂ (List.replicate (n-s+2) 0 ++ (backgroundDegrees l).map Int.ofNat))]
      simp_rw [finiteBackgroundAmplitude_zeros]
end WP
