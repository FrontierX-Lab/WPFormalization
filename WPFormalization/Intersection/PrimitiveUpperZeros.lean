import WPFormalization.Intersection.PrimitiveGenusTwo
/-! Actual zero-entry upper estimates used by the Appendix B induction.
The genus-one/two one-zero estimate is unconditional relative to PsiTheory.
The general one-zero lemma explicitly takes the lower-complexity positive
majorant that will be supplied by strong induction; this is not an added
PsiTheory field or an assumption of the original primitive_bounds statement. -/
noncomputable section
namespace WP
lemma signedPrimitive_zero_upper_step (P : PsiTheory) (g : ℕ) (d : List ℤ) (B : ℝ)
    (hd : ∀ k ∈ d, 0 ≤ k) (hh : 2 ≤ complexity g (d.length+1))
    (hm : ∀ j ∈ Finset.range d.length, 0 < d[j]! →
      signedPureC P g ((d[j]!-1) :: d.eraseIdx j) ≤ B) :
    signedPureC P g (0 :: d) ≤
      ((∑ j ∈ Finset.range d.length, if 0 < d[j]! then (2*(d[j]! : ℝ)+1) else 0) /
        (3*((complexity g (d.length+1) : ℝ)-1))) * B := by
  have hhR : (2 : ℝ) ≤ complexity g (d.length+1) := by exact_mod_cast hh
  have hden : (0 : ℝ) < 3*((complexity g (d.length+1) : ℝ)-1) := by linarith
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,signedPureC_dvv P g 0 d hd hh]
  simp only [primitiveDvvRHS,Nat.zero_sub,Finset.range_zero,Finset.sum_empty,
    mul_zero,ite_self,add_zero,Int.natCast_zero,zero_add]
  rw [Finset.sum_div,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hv : 0 ≤ d[j]! := by
    apply hd
    simpa [hj'] using (List.getElem_mem (l := d) j hj')
  have hvR : (0 : ℝ) ≤ (d[j]! : ℝ) := by exact_mod_cast hv
  have hcoef : 0 ≤ (2*(d[j]! : ℝ)+1)/(3*((complexity g (d.length+1) : ℝ)-1)) :=
    div_nonneg (by linarith) hden.le
  by_cases hp : 0 < d[j]!
  · rw [if_pos hp]
    exact mul_le_mul_of_nonneg_left (hm j hj hp) hcoef
  · rw [if_neg hp]
    have hv0 : d[j]! = 0 := by omega
    have hz : signedPureC P g ((d[j]!-1) :: d.eraseIdx j) = 0 := by
      apply signedPureC_vanish
      right; left
      exact ⟨-1,by simp [hv0],by norm_num⟩
    rw [hz]
    simp
lemma signedPureC_toNat (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hd : ∀ k ∈ d, 0 ≤ k) : signedPureC P g d = pureC P g (d.map Int.toNat) := by
  rw [pureC_signed,map_ofNat_toNat d hd]
lemma signedPureC_genus_two_lt (P : PsiTheory) (d : List ℤ)
    (hd : ∀ k ∈ d, 0 < k) (hdim : d.sum = 3*(2 : ℤ)-3+d.length) :
    signedPureC P 2 d < 3/11 := by
  have hdn : ∀ k ∈ d, 0 ≤ k := fun k hk => (hd k hk).le
  rw [signedPureC_toNat P 2 d hdn]
  apply pureC_genus_two_lt P (d.map Int.toNat)
  · intro k hk
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
    have := hd j hj
    omega
  · have he : ((d.map Int.toNat).sum : ℤ) = d.sum := by
      rw [← sum_map_int,map_ofNat_toNat d hdn]
    have hcast := dimension_cast_of_stable 2 d.length (by unfold Stable; omega)
    simp only [List.length_map]
    exact_mod_cast (show ((d.map Int.toNat).sum : ℤ) = (dimension 2 d.length : ℤ) by omega)
lemma signedPureC_genus_one_positive (P : PsiTheory) (d : List ℤ)
    (hs : Stable 1 d.length) (hd : ∀ k ∈ d, 0 < k)
    (hdim : d.sum = 3*(1 : ℤ)-3+d.length) : signedPureC P 1 d = 1/6 := by
  have hdn : ∀ k ∈ d, 0 ≤ k := fun k hk => (hd k hk).le
  rw [signedPureC_toNat P 1 d hdn]
  apply pureC_genus_one P (d.map Int.toNat)
  · simp only [List.length_map]
    unfold Stable at hs
    omega
  · intro k hk
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
    have := hd j hj
    omega
  · have he : ((d.map Int.toNat).sum : ℤ) = d.sum := by
      rw [← sum_map_int,map_ofNat_toNat d hdn]
    have hcast := dimension_cast_of_stable 1 d.length hs
    simp only [List.length_map]
    exact_mod_cast (show ((d.map Int.toNat).sum : ℤ) = (dimension 1 d.length : ℤ) by omega)
lemma signed_small_genus_one_zero_upper_aux (P : PsiTheory) (N : ℕ) :
    ∀ g : ℕ, ∀ d : List ℤ, g = 1 ∨ g = 2 → d.length = N → Stable g d.length →
      (∀ k ∈ d, 0 ≤ k) → d.count 0 ≤ 1 →
      d.sum = 3*(g : ℤ)-3+d.length → signedPureC P g d ≤ 1/3 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro g d hg he hs hd hz hdim
    have hg1 : 1 ≤ g := by omega
    by_cases hone : (1 : ℤ) ∈ d
    · let t := d.erase 1
      have hp : d.Perm (1 :: t) := List.perm_cons_erase hone
      have hl : d.length = t.length+1 := by simpa using hp.length_eq
      have ht : ∀ k ∈ t, 0 ≤ k := fun k hk => hd k (List.mem_of_mem_erase hk)
      have hdim' : t.sum = 3*(g : ℤ)-3+t.length := by
        have hh := hp.sum_eq
        simp only [List.sum_cons] at hh
        rw [hl] at hdim
        push_cast at hdim
        omega
      rw [signedPureC_perm P g hp]
      by_cases hst : Stable g t.length
      · rw [signedPureC_dilaton P g t hst]
        exact ih t.length (by omega) g t hg rfl hst ht
          (le_trans (List.Sublist.count_le 0 (List.erase_sublist)) hz) hdim'
      · have hg' : g = 1 := by unfold Stable at hst; omega
        have htlen : t.length = 0 := by unfold Stable at hst; omega
        have ht0 : t = [] := List.length_eq_zero_iff.mp htlen
        rw [hg',ht0]
        norm_num [signedPureC,primitiveScale,weighted,doubleWeight,complexity,
          oddFactorial,Finset.prod_range_succ,P.base₁]
    · by_cases hzero : (0 : ℤ) ∈ d
      · let t := d.erase 0
        have hp : d.Perm (0 :: t) := List.perm_cons_erase hzero
        have hl : d.length = t.length+1 := by simpa using hp.length_eq
        have hcount := hp.count_eq 0
        simp only [List.count_cons,beq_self_eq_true,ite_true] at hcount
        have hzt : t.count 0 = 0 := by omega
        have ht : ∀ k ∈ t, 2 ≤ k := by
          intro k hk
          have hk' := List.mem_of_mem_erase hk
          have hk0 := hd k hk'
          have hk1 : k ≠ 1 := fun h => hone (h ▸ hk')
          have hkz : k ≠ 0 := fun h => (List.count_eq_zero.mp hzt) (h ▸ hk)
          omega
        have hdim' : (0 :: t).sum = 3*(g : ℤ)-3+(t.length+1) := by
          rw [← hp.sum_eq]
          simpa only [hl,Nat.cast_add,Nat.cast_one] using hdim
        rw [signedPureC_perm P g hp]
        rcases hg with rfl | rfl
        · have hs0 : 2*(t.length : ℤ) ≤ t.sum := twice_length_le_sum t ht
          have hn1 : t.length = 1 := by
            simp only [List.sum_cons,zero_add] at hdim'
            have hn : 1 ≤ t.length := by
              by_contra h
              have ht0 : t = [] := List.length_eq_zero_iff.mp (by omega)
              rw [ht0] at hdim'; norm_num at hdim'
            omega
          obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp hn1
          rw [ha] at hdim' ⊢
          have ha2 : a = 2 := by simpa using hdim'
          rw [ha2]
          norm_num [signedPureC,primitiveScale,weighted,doubleWeight,complexity,
            oddFactorial,Finset.prod_range_succ,psi_1_0_2]
        · have htn : 1 ≤ t.length := by
            by_contra h
            have ht0 : t = [] := List.length_eq_zero_iff.mp (by omega)
            rw [ht0] at hdim'; norm_num at hdim'
          have hh : 2 ≤ complexity 2 (t.length+1) := by unfold complexity; omega
          have hb := signedPrimitive_zero_upper_step P 2 t (3/11)
            (fun k hk => le_trans (by norm_num) (ht k hk)) hh
            (by
              intro j hj hpj
              have hj' := Finset.mem_range.mp hj
              apply (signedPureC_genus_two_lt P ((t[j]!-1) :: t.eraseIdx j) ?_ ?_).le
              · intro k hk
                rcases List.mem_cons.mp hk with hk | hk
                · subst k
                  have hv : 2 ≤ t[j]! := by
                    apply ht
                    simpa [hj'] using (List.getElem_mem (l := t) j hj')
                  omega
                · have := ht k (List.mem_of_mem_eraseIdx hk); omega
              · simpa only [zero_add,Nat.cast_ofNat] using merger_dimension 2 0 t hdim' j hj')
          have hw := sum_positive_string_weights t (fun k hk => le_trans (by norm_num) (ht k hk))
          rw [hzt] at hw
          rw [hw] at hb
          simp only [Nat.cast_zero] at hb
          have hsumR : (t.sum : ℝ) = 3+(t.length+1) := by
            simp only [List.sum_cons,zero_add] at hdim'
            exact_mod_cast hdim'
          have hc : (complexity 2 (t.length+1) : ℝ) = (t.length : ℝ)+3 := by
            unfold complexity
            rw [Nat.cast_sub (by omega)]
            push_cast
            ring
          have hnR : (1 : ℝ) ≤ t.length := by exact_mod_cast htn
          have hden : (0 : ℝ) < 3*((t.length : ℝ)+2) := by positivity
          have hbound : ((2*(t.sum : ℝ)+t.length-0)/(3*((complexity 2 (t.length+1) : ℝ)-1)))*(3/11) ≤ 1/3 := by
            rw [hsumR,hc]
            rw [show (t.length : ℝ)+3-1 = t.length+2 by ring]
            field_simp [show (t.length : ℝ)+2 ≠ 0 by positivity]
            nlinarith
          exact hb.trans hbound
      · have hpos : ∀ k ∈ d, 0 < k := by
          intro k hk
          have hn := hd k hk
          have hz' : k ≠ 0 := fun h => hzero (h ▸ hk)
          omega
        rcases hg with rfl | rfl
        · rw [signedPureC_genus_one_positive P d hs hpos hdim]
          norm_num
        · exact (signedPureC_genus_two_lt P d hpos hdim).le.trans (by norm_num)
lemma signedPrimitive_one_zero_upper_aux (P : PsiTheory) (H : ℕ)
    (hpositive : ∀ g' c, 1 ≤ g' → Stable g' c.length → (∀ k ∈ c, 0 < k) →
      c.sum = 3*(g' : ℤ)-3+c.length → complexity g' c.length < H →
      signedPureC P g' c ≤ primitiveMajorant (complexity g' c.length)) (N : ℕ) :
    ∀ g : ℕ, ∀ d : List ℤ, 1 ≤ g → d.length = N → Stable g d.length →
      (∀ k ∈ d, 0 ≤ k) → d.count 0 ≤ 1 →
      d.sum = 3*(g : ℤ)-3+d.length → complexity g d.length < H → signedPureC P g d ≤ 1 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro g d hg he hs hd hz hdim hH
    by_cases hone : (1 : ℤ) ∈ d
    · let t := d.erase 1
      have hp : d.Perm (1 :: t) := List.perm_cons_erase hone
      have hl : d.length = t.length+1 := by simpa using hp.length_eq
      have ht : ∀ k ∈ t, 0 ≤ k := fun k hk => hd k (List.mem_of_mem_erase hk)
      have hdim' : t.sum = 3*(g : ℤ)-3+t.length := by
        have hh := hp.sum_eq
        simp only [List.sum_cons] at hh
        rw [hl] at hdim
        push_cast at hdim
        omega
      rw [signedPureC_perm P g hp]
      by_cases hst : Stable g t.length
      · rw [signedPureC_dilaton P g t hst]
        apply ih t.length (by omega) g t hg rfl hst ht
          (le_trans (List.Sublist.count_le 0 (List.erase_sublist)) hz) hdim'
        unfold complexity at hH ⊢
        rw [hl] at hH
        omega
      · have hg' : g = 1 := by unfold Stable at hst; omega
        have htlen : t.length = 0 := by unfold Stable at hst; omega
        have ht0 : t = [] := List.length_eq_zero_iff.mp htlen
        rw [hg',ht0]
        norm_num [signedPureC,primitiveScale,weighted,doubleWeight,complexity,
          oddFactorial,Finset.prod_range_succ,P.base₁]
    · by_cases hzero : (0 : ℤ) ∈ d
      · let t := d.erase 0
        have hp : d.Perm (0 :: t) := List.perm_cons_erase hzero
        have hl : d.length = t.length+1 := by simpa using hp.length_eq
        have hcount := hp.count_eq 0
        simp only [List.count_cons,beq_self_eq_true,ite_true] at hcount
        have hzt : t.count 0 = 0 := by omega
        have ht : ∀ k ∈ t, 2 ≤ k := by
          intro k hk
          have hk' := List.mem_of_mem_erase hk
          have hk0 := hd k hk'
          have hk1 : k ≠ 1 := fun h => hone (h ▸ hk')
          have hkz : k ≠ 0 := fun h => (List.count_eq_zero.mp hzt) (h ▸ hk)
          omega
        have hdim' : (0 :: t).sum = 3*(g : ℤ)-3+(t.length+1) := by
          rw [← hp.sum_eq]
          simpa only [hl,Nat.cast_add,Nat.cast_one] using hdim
        have hh : 2 ≤ complexity g (t.length+1) := by
          by_contra hh
          have h0 : g = 1 ∧ t.length = 0 := by unfold complexity at hh; omega
          have ht0 : t = [] := List.length_eq_zero_iff.mp h0.2
          rw [h0.1,ht0] at hdim'
          norm_num at hdim'
        rw [signedPureC_perm P g hp]
        have hb := signedPrimitive_zero_upper_step P g t
          (primitiveMajorant ((complexity g (t.length+1) : ℝ)-1))
          (fun k hk => le_trans (by norm_num) (ht k hk)) hh
          (by
            intro j hj hpj
            have hj' := Finset.mem_range.mp hj
            let c := (t[j]!-1) :: t.eraseIdx j
            have hlen : c.length = t.length := by
              dsimp only [c]
              simp only [List.length_cons,List.length_eraseIdx_of_lt hj']
              omega
            have hcp : ∀ k ∈ c, 0 < k := by
              intro k hk
              rcases List.mem_cons.mp hk with hk | hk
              · subst k
                have hv : 2 ≤ t[j]! := by
                  apply ht
                  simpa [hj'] using (List.getElem_mem (l := t) j hj')
                omega
              · have := ht k (List.mem_of_mem_eraseIdx hk); omega
            have hst : Stable g c.length := by
              rw [hlen]
              unfold Stable
              unfold complexity at hh
              omega
            have hc : complexity g c.length+1 = complexity g d.length := by
              rw [hlen,hl]
              unfold complexity
              omega
            have hH' : complexity g c.length < H := by omega
            have hcR : (complexity g c.length : ℝ) = (complexity g (t.length+1) : ℝ)-1 := by
              rw [hl] at hc
              have hc' : (complexity g c.length : ℝ)+1 = (complexity g (t.length+1) : ℝ) := by exact_mod_cast hc
              linarith
            have hbound := hpositive g c hg hst hcp (by simpa only [c,zero_add] using merger_dimension g 0 t hdim' j hj') hH'
            rw [hcR] at hbound
            exact hbound)
        have hw := sum_positive_string_weights t (fun k hk => le_trans (by norm_num) (ht k hk))
        rw [hzt] at hw
        rw [hw] at hb
        simp only [Nat.cast_zero] at hb
        have hsumR : (t.sum : ℝ) = 3*(g : ℝ)-3+(t.length+1) := by
          simp only [List.sum_cons,zero_add] at hdim'
          exact_mod_cast hdim'
        have hc : (complexity g (t.length+1) : ℝ) = 2*(g : ℝ)+t.length-1 := by
          unfold complexity
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        have hhR : (2 : ℝ) ≤ complexity g (t.length+1) := by exact_mod_cast hh
        have heq : (2*(t.sum : ℝ)+t.length-0)/(3*((complexity g (t.length+1) : ℝ)-1)) =
            1+2/(3*((complexity g (t.length+1) : ℝ)-1)) := by
          field_simp [show (complexity g (t.length+1) : ℝ)-1 ≠ 0 by linarith]
          rw [hc]
          nlinarith [hsumR]
        rw [heq] at hb
        exact hb.trans (primitiveMajorant_one_zero hhR)
      · have hpos : ∀ k ∈ d, 0 < k := by
          intro k hk
          have hn := hd k hk
          have hz' : k ≠ 0 := fun h => hzero (h ▸ hk)
          omega
        exact (hpositive g d hg hs hpos hdim hH).trans (primitiveMajorant_le_one _)
end WP
