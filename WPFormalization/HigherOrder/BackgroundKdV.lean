import WPFormalization.HigherOrder.FiniteKdV
import WPFormalization.External.KdV

/-! Exact transformation of the classical first KdV descendant law into finite
exponential-background amplitudes. The coefficient 3 comes from the actual
odd double factorial of the distinguished degree-one marking, so the original
1/12 and 1/2 become 1/4 and 3/2. All background subset and binomial/Cauchy-product
transformations are proved in FiniteKdV for arbitrary finite background times.
-/
noncomputable section
namespace WP
lemma finiteBackgroundAmplitude_one_zeros (P : PsiTheory) (g p : ℕ) {N : ℕ}
    (B m : ℕ) (t : Fin N → ℝ) :
    finiteBackgroundAmplitude P g (1 :: List.replicate p 0) B m t =
      3*∑ l ∈ backgroundVectors N B m,
        (∏ i, t i^(l i)/(l i).factorial)*
          P.psi g (1 :: List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat) := by
  have ho : oddFactorial 0 = 1 := by norm_num [oddFactorial]
  have h1 : oddFactorial 1 = 3 := by norm_num [oddFactorial,Finset.prod_range_succ]
  unfold finiteBackgroundAmplitude doubleWeight
  simp only [List.map_cons,List.map_replicate,Int.toNat_zero,Int.toNat_one,
    ho,h1,Nat.cast_one,Nat.cast_ofNat,List.prod_cons,List.prod_replicate,one_pow,mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  ring

lemma background_kdv_tail (P : PsiTheory) (g p : ℕ) (hg : 1 ≤ g) (hp : 2 ≤ p)
    {N : ℕ} (l : Fin N → ℕ) :
    P.psi g (1 :: List.replicate (p-1) 0 ++ (backgroundDegrees l).map Int.ofNat) =
      P.psi (g-1) (List.replicate (p+2) 0 ++ (backgroundDegrees l).map Int.ofNat)/12 +
      (1/2 : ℝ)*∑ j ∈ Finset.range (g+1),
        ∑ I ∈ (Finset.range (List.replicate (p-2) 0 ++ (backgroundDegrees l).map Int.ofNat).length).powerset,
          P.psi j (List.replicate 2 0 ++ selected (List.replicate (p-2) 0 ++ (backgroundDegrees l).map Int.ofNat) I)*
            P.psi (g-j) (List.replicate 2 0 ++ selected (List.replicate (p-2) 0 ++ (backgroundDegrees l).map Int.ofNat)
              ((Finset.range (List.replicate (p-2) 0 ++ (backgroundDegrees l).map Int.ofNat).length) \ I)) := by
  have hL : ∀ k ∈ List.replicate (p-2) (0 : ℤ) ++ (backgroundDegrees l).map Int.ofNat, 0 ≤ k := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · have he := (List.mem_replicate.mp hk).2
      omega
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hk
      exact Int.natCast_nonneg a
  have he := External.first_kdv_descendants P g hg
    (List.replicate (p-2) 0 ++ (backgroundDegrees l).map Int.ofNat) hL
  have htail : (1 : ℤ) :: List.replicate (p-1) 0 ++ (backgroundDegrees l).map Int.ofNat =
      1 :: 0 :: (List.replicate (p-2) 0 ++ (backgroundDegrees l).map Int.ofNat) := by
    rw [show p-1 = (p-2)+1 by omega,List.replicate_succ]
    rfl
  have hgenus : List.replicate 4 (0 : ℤ) ++ (List.replicate (p-2) 0 ++ (backgroundDegrees l).map Int.ofNat) =
      List.replicate (p+2) 0 ++ (backgroundDegrees l).map Int.ofNat := by
    rw [← List.append_assoc,← List.replicate_add]
    rw [show 4+(p-2) = p+2 by omega]
  rwa [← htail,hgenus] at he

lemma finite_background_kdv (P : PsiTheory) (g p : ℕ) (hg : 1 ≤ g) (hp : 2 ≤ p)
    {N B M : ℕ} (hM : M ≤ B) (t : Fin N → ℝ) :
    finiteBackgroundAmplitude P g (1 :: List.replicate (p-1) 0) B M t =
      (1/4 : ℝ)*finiteBackgroundAmplitude P (g-1) (List.replicate (p+2) 0) B M t +
      (3/2 : ℝ)*∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (p-1), (Nat.choose (p-2) s : ℝ)*
        ∑ k ∈ Finset.range (M+1),
          finiteBackgroundAmplitude P j (List.replicate (s+2) 0) B k t *
            finiteBackgroundAmplitude P (g-j) (List.replicate (p-s) 0) B (M-k) t := by
  rw [finiteBackgroundAmplitude_one_zeros]
  simp only [background_kdv_tail P g p hg hp, mul_add,← mul_div_assoc,
    Finset.sum_add_distrib,← Finset.sum_div]
  have hscale (l : Fin N → ℕ) (F : ℕ → ℝ) :
      (∏ i, t i^(l i)/(l i).factorial)*((1/2 : ℝ)*∑ j ∈ Finset.range (g+1),F j) =
        (1/2 : ℝ)*∑ j ∈ Finset.range (g+1), (∏ i, t i^(l i)/(l i).factorial)*F j := by
    rw [← Finset.mul_sum]
    ring
  simp_rw [hscale]
  rw [← Finset.mul_sum,Finset.sum_comm]
  have hsplit (j : ℕ) := finite_background_zero_split P j (g-j) (p-2) hM t
  simp_rw [hsplit]
  have hr : p-2+1 = p-1 := by omega
  rw [hr]
  have htuple (s : ℕ) (hs : s ∈ Finset.range (p-1)) : p-2-s+2 = p-s := by
    have hh := Finset.mem_range.mp hs
    omega
  have he :
      (∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (p-1), (Nat.choose (p-2) s : ℝ)*
        ∑ k ∈ Finset.range (M+1),
          finiteBackgroundAmplitude P j (List.replicate (s+2) 0) B k t *
            finiteBackgroundAmplitude P (g-j) (List.replicate (p-2-s+2) 0) B (M-k) t) =
      (∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (p-1), (Nat.choose (p-2) s : ℝ)*
        ∑ k ∈ Finset.range (M+1),
          finiteBackgroundAmplitude P j (List.replicate (s+2) 0) B k t *
            finiteBackgroundAmplitude P (g-j) (List.replicate (p-s) 0) B (M-k) t) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro s hs
    rw [htuple s hs]
  rw [he,← finiteBackgroundAmplitude_zeros P (g-1) (p+2) B M t]
  ring
end WP
