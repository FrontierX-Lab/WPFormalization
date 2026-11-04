import WPFormalization.Intersection.PrimitiveUpperZeros
import WPFormalization.Intersection.PrimitiveSeparating
/-! Actual one- and two-zero endpoint estimates, together with the upper
normalized-DVV induction step. All child majorants remain explicit local
induction hypotheses; no new field is added to the classical interface. -/
noncomputable section
namespace WP
/-- The finite-complexity positive child bound supplied by the intended induction. -/
def primitivePositiveBound (P : PsiTheory) (g K : ℕ) (B : ℝ) : Prop :=
  ∀ c : List ℤ, Stable g c.length → (∀ k ∈ c, 0 < k) →
    c.sum = 3*(g : ℤ)-3+c.length → complexity g c.length ≤ K → signedPureC P g c ≤ B
lemma signedPrimitive_zero_core_upper (P : PsiTheory) (g K : ℕ) (B : ℝ)
    (hg : 2 ≤ g) (d : List ℤ) (hd : ∀ k ∈ d, 2 ≤ k)
    (hdim : (0 :: d).sum = 3*(g : ℤ)-3+(d.length+1))
    (hK : complexity g d.length ≤ K) (hupp : primitivePositiveBound P g K B) :
    signedPureC P g (0 :: d) ≤
      (1+2/(3*((complexity g (d.length+1) : ℝ)-1)))*B := by
  have hh : 2 ≤ complexity g (d.length+1) := by unfold complexity; omega
  have hhR : (2 : ℝ) ≤ complexity g (d.length+1) := by exact_mod_cast hh
  have hcp : complexity g (d.length+1) = complexity g d.length+1 := by unfold complexity; omega
  have hb := signedPrimitive_zero_upper_step P g d B
    (fun k hk => le_trans (by norm_num) (hd k hk)) hh
    (by
      intro j hj hjpos
      have hj' := Finset.mem_range.mp hj
      let c := (d[j]!-1) :: d.eraseIdx j
      have hlen : c.length = d.length := by
        dsimp only [c]
        simp only [List.length_cons,List.length_eraseIdx_of_lt hj']
        omega
      apply hupp c
      · unfold Stable
        rw [hlen]
        omega
      · intro k hk
        rcases List.mem_cons.mp hk with hk | hk
        · subst k
          have hv : 2 ≤ d[j]! := by
            apply hd
            simpa [hj'] using (List.getElem_mem (l := d) j hj')
          omega
        · have := hd k (List.mem_of_mem_eraseIdx hk); omega
      · simpa only [c,zero_add] using merger_dimension g 0 d hdim j hj'
      · simpa only [hlen] using hK)
  have hz : d.count 0 = 0 := List.count_eq_zero.mpr (fun hm => by have := hd 0 hm; omega)
  have hw := sum_positive_string_weights d (fun k hk => le_trans (by norm_num) (hd k hk))
  rw [hz] at hw
  rw [hw] at hb
  simp only [Nat.cast_zero] at hb
  have hsumR : (d.sum : ℝ) = 3*(g : ℝ)-3+(d.length+1) := by
    simp only [List.sum_cons,zero_add] at hdim
    exact_mod_cast hdim
  have hc : (complexity g (d.length+1) : ℝ) = 2*(g : ℝ)+d.length-1 := by
    unfold complexity
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have heq : (2*(d.sum : ℝ)+d.length-0)/(3*((complexity g (d.length+1) : ℝ)-1)) =
      1+2/(3*((complexity g (d.length+1) : ℝ)-1)) := by
    field_simp [show (complexity g (d.length+1) : ℝ)-1 ≠ 0 by linarith]
    rw [hc]
    nlinarith [hsumR]
  rw [heq] at hb
  exact hb
lemma signedPrimitive_zero_one_node_upper (P : PsiTheory) (g K : ℕ) (B : ℝ)
    (hg : 2 ≤ g) (hB : 0 ≤ B) (k : ℤ) (hk : 1 ≤ k) (d : List ℤ)
    (hd : ∀ j ∈ d, 2 ≤ j)
    (hdim : (0 :: k :: d).sum = 3*(g : ℤ)-3+(d.length+2))
    (hK : complexity g (d.length+1) ≤ K) (hupp : primitivePositiveBound P g K B) :
    signedPureC P g (0 :: k :: d) ≤
      (1+2/(3*((complexity g (d.length+2) : ℝ)-2)))*B := by
  have hZ : (3 : ℝ) ≤ complexity g (d.length+2) := by
    exact_mod_cast (show 3 ≤ complexity g (d.length+2) by unfold complexity; omega)
  by_cases hk1 : k = 1
  · subst k
    rw [signedPureC_perm P g (List.Perm.swap (1 : ℤ) 0 d),
      signedPureC_dilaton P g (0 :: d) (by unfold Stable; simp; omega)]
    have hdim' : (0 :: d).sum = 3*(g : ℤ)-3+(d.length+1) := by
      simp only [List.sum_cons] at hdim ⊢
      omega
    have hK' : complexity g d.length ≤ K := by unfold complexity at *; omega
    have hb := signedPrimitive_zero_core_upper P g K B hg d hd hdim' hK' hupp
    have hc : (complexity g (d.length+1) : ℝ)-1 = (complexity g (d.length+2) : ℝ)-2 := by
      have hh : complexity g (d.length+2) = complexity g (d.length+1)+1 := by unfold complexity; omega
      rw [hh,Nat.cast_add,Nat.cast_one]
      ring
    rw [hc] at hb
    exact hb
  · have hk₂ : 2 ≤ k := by omega
    have hb := signedPrimitive_zero_core_upper P g K B hg (k :: d)
      (by intro j hj; rcases List.mem_cons.mp hj with hj | hj; subst j; exact hk₂; exact hd j hj)
      (by simpa only [List.length_cons,Nat.cast_add,Nat.cast_one,show (d.length : ℤ)+1+1=d.length+2 by omega] using hdim)
      (by simpa only [List.length_cons] using hK) hupp
    have hfrac : (2 : ℝ)/(3*((complexity g (d.length+2) : ℝ)-1)) ≤
        2/(3*((complexity g (d.length+2) : ℝ)-2)) := by
      apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < 3*((complexity g (d.length+2) : ℝ)-1))
        (by linarith : (0 : ℝ) < 3*((complexity g (d.length+2) : ℝ)-2))).mpr
      linarith
    apply hb.trans
    simp only [List.length_cons]
    rw [show d.length+1+1=d.length+2 by omega]
    exact mul_le_mul_of_nonneg_right (by linarith) hB
lemma signedPrimitive_two_zero_upper (P : PsiTheory) (g K : ℕ) (B : ℝ)
    (hg : 2 ≤ g) (hB : 0 ≤ B) (d : List ℤ) (hd : ∀ k ∈ d, 2 ≤ k)
    (hdim : (0 :: 0 :: d).sum = 3*(g : ℤ)-3+(d.length+2))
    (hK : complexity g d.length ≤ K) (hupp : primitivePositiveBound P g K B) :
    signedPureC P g (0 :: 0 :: d) ≤
      (1+1/(3*((complexity g (d.length+2) : ℝ)-1)))*
        (1+2/(3*((complexity g (d.length+2) : ℝ)-3)))*B := by
  have hZ : (4 : ℝ) ≤ complexity g (d.length+2) := by
    exact_mod_cast (show 4 ≤ complexity g (d.length+2) by unfold complexity; omega)
  have hc : complexity g (d.length+2) = complexity g (d.length+1)+1 := by unfold complexity; omega
  have hcR : (complexity g (d.length+2) : ℝ) = (complexity g (d.length+1) : ℝ)+1 := by exact_mod_cast hc
  have hh : 2 ≤ complexity g ((0 :: d).length+1) := by simp only [List.length_cons]; unfold complexity; omega
  have ht : ∀ k ∈ (0 : ℤ) :: d, 0 ≤ k := by
    intro k hk; rcases List.mem_cons.mp hk with hk | hk
    · subst k; rfl
    · have := hd k hk; omega
  have hb := signedPrimitive_zero_upper_step P g (0 :: d)
    ((1+2/(3*((complexity g (d.length+2) : ℝ)-3)))*B) ht hh
    (by
      intro j hj hjpos
      cases j with
      | zero => simp at hjpos
      | succ j =>
        have hj' : j < d.length := by simpa using Finset.mem_range.mp hj
        have hval : 2 ≤ d[j]! := by
          apply hd
          simpa [hj'] using (List.getElem_mem (l := d) j hj')
        simp only [List.getElem!_cons_succ,List.eraseIdx_cons_succ]
        rw [signedPureC_perm P g (List.Perm.swap (0 : ℤ) (d[j]!-1) (d.eraseIdx j))]
        have hlen : (d.eraseIdx j).length = d.length-1 := List.length_eraseIdx_of_lt hj'
        have hdim' : (0 :: (d[j]!-1) :: d.eraseIdx j).sum =
            3*(g : ℤ)-3+((d.eraseIdx j).length+2) := by
          have he := merger_dimension g 0 (0 :: d) (by
            simpa only [List.length_cons,Nat.cast_add,Nat.cast_one,show (d.length : ℤ)+1+1=d.length+2 by omega] using hdim) (j+1)
            (by simpa using hj')
          simp only [List.getElem!_cons_succ,List.eraseIdx_cons_succ,zero_add,List.sum_cons,
            List.length_cons,Nat.cast_add,Nat.cast_one] at he ⊢
          omega
        have hK' : complexity g ((d.eraseIdx j).length+1) ≤ K := by rw [hlen]; unfold complexity at *; omega
        have hmin : ∀ k ∈ d.eraseIdx j, 2 ≤ k := fun k hk => hd k (List.mem_of_mem_eraseIdx hk)
        have hbound := signedPrimitive_zero_one_node_upper P g K B hg hB (d[j]!-1)
          (by omega) (d.eraseIdx j) hmin hdim' hK' hupp
        have hc' : (complexity g ((d.eraseIdx j).length+2) : ℝ)-2 =
            (complexity g (d.length+2) : ℝ)-3 := by
          have he : complexity g (d.length+2) = complexity g ((d.eraseIdx j).length+2)+1 := by
            rw [hlen]; unfold complexity; omega
          rw [he,Nat.cast_add,Nat.cast_one]
          ring
        rw [hc'] at hbound
        exact hbound)
  have hzd : d.count 0 = 0 := List.count_eq_zero.mpr (fun hm => by have := hd 0 hm; omega)
  have hw := sum_positive_string_weights (0 :: d) ht
  simp only [List.sum_cons,zero_add,List.length_cons,List.count_cons,
    beq_self_eq_true,ite_true,hzd,zero_add,Nat.cast_add,Nat.cast_one] at hw
  simp only [List.length_cons] at hb
  rw [hw] at hb
  rw [show d.length+1+1=d.length+2 by omega] at hb
  have hsumR : (d.sum : ℝ) = 3*(g : ℝ)-3+(d.length+2) := by
    simp only [List.sum_cons,zero_add] at hdim
    exact_mod_cast hdim
  have hc' : (complexity g (d.length+2) : ℝ) = 2*(g : ℝ)+d.length := by
    unfold complexity
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have heq : (2*(d.sum : ℝ)+(d.length+1)-1)/(3*((complexity g (d.length+2) : ℝ)-1)) =
      1+1/(3*((complexity g (d.length+2) : ℝ)-1)) := by
    field_simp [show (complexity g (d.length+2) : ℝ)-1 ≠ 0 by linarith]
    rw [hc']
    nlinarith [hsumR]
  rw [heq] at hb
  simpa only [mul_assoc] using hb
lemma doubleZeroStringFactor_expansion (h : ℝ) (hh : 8 ≤ h) :
    (1+1/(3*(h-2)))*(1+2/(3*(h-4))) = doubleZeroStringFactor h := by
  unfold doubleZeroStringFactor
  have h₂ : h-2 ≠ 0 := by linarith
  have h₄ : h-4 ≠ 0 := by linarith
  have h₆ : 3*h-6 ≠ 0 := by linarith
  have h₁₂ : 3*h-12 ≠ 0 := by linarith
  field_simp [h₂,h₄,h₆,h₁₂]
  <;> ring
lemma signedPrimitive_upper_from_children (P : PsiTheory) (g pivot : ℕ) (d : List ℤ)
    (hg : 1 ≤ g) (hp : 1 ≤ pivot) (hd : ∀ k ∈ d, 0 ≤ k)
    (hh : 2 ≤ complexity g (d.length+1))
    (hdim : ((pivot : ℤ) :: d).sum = 3*(g : ℤ)-3+(d.length+1))
    (B M S : ℝ)
    (hm : ∀ j ∈ Finset.range d.length,
      signedPureC P g (((pivot : ℤ)+d[j]!-1) :: d.eraseIdx j) ≤ B)
    (hn : (∑ u ∈ Finset.range (pivot-1), signedPureC P (g-1) ((u : ℤ) :: ((pivot : ℤ)-2-u) :: d)) ≤
      (pivot-1 : ℕ)*B+M)
    (hs : (∑ u ∈ Finset.range (pivot-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        primitiveSeparatingTerm P g pivot d u g₁ I) ≤ S) :
    signedPureC P g ((pivot : ℤ) :: d) ≤
      B+(2/(3*((complexity g (d.length+1) : ℝ)-1)))*M+S := by
  have hhR : (2 : ℝ) ≤ complexity g (d.length+1) := by exact_mod_cast hh
  have hden : (0 : ℝ) < 3*((complexity g (d.length+1) : ℝ)-1) := by linarith
  have hcoef : ∀ j ∈ Finset.range d.length,
      0 ≤ (2*(d[j]! : ℝ)+1)/(3*((complexity g (d.length+1) : ℝ)-1)) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hv : 0 ≤ d[j]! := by
      apply hd
      simpa [hj'] using (List.getElem_mem (l := d) j hj')
    have hvR : (0 : ℝ) ≤ (d[j]! : ℝ) := by exact_mod_cast hv
    exact div_nonneg (by linarith) hden.le
  have hlinear := sum_linear_primitive_weights g pivot d hp hh hdim
  have heq :
      (∑ j ∈ Finset.range d.length,
        ((2*(d[j]! : ℝ)+1)/(3*((complexity g (d.length+1) : ℝ)-1))) * B) +
      (2/(3*((complexity g (d.length+1) : ℝ)-1))) * ((pivot-1 : ℕ)*B+M) + S =
      B+(2/(3*((complexity g (d.length+1) : ℝ)-1)))*M+S := by
    simp only [← Finset.sum_mul,← Finset.sum_div]
    field_simp [show (complexity g (d.length+1) : ℝ)-1 ≠ 0 by linarith]
    linear_combination B*hlinear
  rw [signedPureC_dvv P g pivot d hd hh]
  unfold primitiveDvvRHS
  rw [if_neg (by omega : g ≠ 0)]
  rw [← heq]
  apply add_le_add
  · apply add_le_add
    · apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hm j hj) (hcoef j hj)
    · exact mul_le_mul_of_nonneg_left hn (div_nonneg (by norm_num) hden.le)
  · simpa only [primitiveSeparatingTerm] using hs
end WP
