import WPFormalization.HigherOrder.BackgroundKdV

/-! The original shifted KdV identity on the full closed parameter interval.
The finite identity is specialized to the actual background times. Dimension
support selects exactly one compatible pair of component deficits, including
unstable zero components; the exact critical specialization handles Y=y₀.
Only the classical unshifted first KdV descendant identity is deferred.
-/
noncomputable section
namespace WP
lemma shifted_kdv_proof (P : PsiTheory) (g p : ℕ) (hg : 1 ≤ g) (hp : 2 ≤ p)
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    normalized P g (1 :: List.replicate (p-1) 0) Y =
      normalized P (g-1) (List.replicate (p+2) 0) Y/4 +
      (3/2 : ℝ)*∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (p-1),
        (Nat.choose (p-2) s : ℝ)*normalized P j (List.replicate (s+2) 0) Y*
          normalized P (g-j) (List.replicate (p-s) 0) Y := by
  let M := dimension g p-1
  let t := closedBackgroundTime M Y
  have hMcast : (M : ℤ) = 3*(g : ℤ)+(p : ℤ)-4 := by
    have hnat : M+4 = 3*g+p := by dsimp [M,dimension]; omega
    have he : ((M+4 : ℕ) : ℤ) = ((3*g+p : ℕ) : ℤ) := congrArg Nat.cast hnat
    push_cast at he
    omega
  have hleftdim : (1 :: List.replicate (p-1) (0 : ℤ)).sum+(M : ℤ) =
      3*(g : ℤ)-3+(1 :: List.replicate (p-1) (0 : ℤ)).length := by
    simp only [List.sum_cons,List.sum_replicate,add_zero,List.length_cons,List.length_replicate,nsmul_zero,Nat.cast_add,Nat.cast_one]
    have hpl : ((p-1 : ℕ) : ℤ) = (p : ℤ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
    rw [hpl,hMcast]
    ring
  have hgenusdim : (List.replicate (p+2) (0 : ℤ)).sum+(M : ℤ) =
      3*((g-1 : ℕ) : ℤ)-3+(List.replicate (p+2) (0 : ℤ)).length := by
    simp only [List.sum_replicate,List.length_replicate]
    rw [Nat.cast_sub hg]
    push_cast
    rw [hMcast]
    ring
  have hleft := finiteBackgroundAmplitude_signed_normalized_closed P g
    (1 :: List.replicate (p-1) 0) Y hY M M M (by omega) le_rfl hleftdim
  have hgenus := finiteBackgroundAmplitude_signed_normalized_closed P (g-1)
    (List.replicate (p+2) 0) Y hY M M M (by omega) le_rfl hgenusdim
  have hl : finiteBackgroundAmplitude P g (1 :: List.replicate (p-1) 0) M M t =
      normalized P g (1 :: List.replicate (p-1) 0) Y := by
    simpa using hleft
  have hge : finiteBackgroundAmplitude P (g-1) (List.replicate (p+2) 0) M M t =
      normalized P (g-1) (List.replicate (p+2) 0) Y := by
    simpa using hgenus
  have hconv (j : ℕ) (hj : j ∈ Finset.range (g+1))
      (s : ℕ) (hs : s ∈ Finset.range (p-1)) :
      (∑ k ∈ Finset.range (M+1),
        finiteBackgroundAmplitude P j (List.replicate (s+2) 0) M k t *
          finiteBackgroundAmplitude P (g-j) (List.replicate (p-s) 0) M (M-k) t) =
      normalized P j (List.replicate (s+2) 0) Y *
        normalized P (g-j) (List.replicate (p-s) 0) Y := by
    have hjg : j ≤ g := by have hh := Finset.mem_range.mp hj; omega
    have hsp : s ≤ p := by have hh := Finset.mem_range.mp hs; omega
    have htotal :
        (List.replicate (s+2) (0 : ℤ)).sum+(List.replicate (p-s) (0 : ℤ)).sum+(M : ℤ) =
        (3*(j : ℤ)-3+(List.replicate (s+2) (0 : ℤ)).length)+
          (3*((g-j : ℕ) : ℤ)-3+(List.replicate (p-s) (0 : ℤ)).length) := by
      simp only [List.sum_replicate,List.length_replicate]
      rw [Nat.cast_sub hjg,Nat.cast_sub hsp]
      push_cast
      rw [hMcast]
      ring
    have he := finiteBackgroundAmplitude_convolution_support_closed P j (g-j)
      (List.replicate (s+2) 0) (List.replicate (p-s) 0) Y hY M M M (by omega) le_rfl htotal
    simpa using he
  have he := finite_background_kdv P g p hg hp (M := M) (B := M) le_rfl t
  rw [hl,hge] at he
  rw [he]
  congr 1
  · ring
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro s hs
    rw [hconv j hj s hs]
    ring

end WP
