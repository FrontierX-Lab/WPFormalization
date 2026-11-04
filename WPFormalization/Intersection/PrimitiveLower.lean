import WPFormalization.Intersection.PrimitiveNormalized
/-! The complete lower half of Appendix B, Lemma B.1, derived from the
classical DVV/string/dilaton interface. The induction proves the stronger
statement for stable positive-genus tuples with at most two zero entries.
Separating terms are dropped only after their actual nonnegativity is proved.
No one-point estimate or general primitive bound is used. -/
noncomputable section
namespace WP
lemma signedPureC_perm (P : PsiTheory) (g : ℕ) {d e : List ℤ} (hp : d.Perm e) :
    signedPureC P g d = signedPureC P g e := by
  unfold signedPureC weighted
  rw [hp.length_eq, doubleWeight_perm hp, P.symmetry g d e hp]
lemma signedPureC_dilaton (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hs : Stable g d.length) : signedPureC P g (1 :: d) = signedPureC P g d := by
  have hc : 2 ≤ complexity g (d.length+1) := by unfold Stable at hs; unfold complexity; omega
  have hr : 2*(g : ℝ)-2+d.length = (complexity g d.length : ℝ) := by
    unfold complexity
    rw [Nat.cast_sub (by unfold Stable at hs; omega)]
    push_cast
    ring
  have hh : (0 : ℝ) < complexity g d.length := by
    exact_mod_cast (show 0 < complexity g d.length by unfold Stable at hs; unfold complexity; omega)
  unfold signedPureC weighted
  simp only [List.length_cons, doubleWeight, List.map_cons, List.prod_cons]
  rw [P.dilaton g d hs, show oddFactorial (1 : ℤ).toNat = 3 by decide,
    primitiveScale_merger g d.length hc, hr]
  have hcc : complexity g (d.length+1) = complexity g d.length+1 := by
    unfold complexity
    unfold Stable at hs
    omega
  rw [hcc, Nat.cast_add, Nat.cast_one]
  push_cast
  field_simp [hh.ne']
  <;> ring
lemma gamma_nat_nonneg (n : ℕ) : (0 : ℝ) ≤ Real.Gamma n := by
  cases n with
  | zero => simp
  | succ n => have hp : (0 : ℝ) < (n+1 : ℕ) := by positivity
              exact (Real.Gamma_pos_of_pos hp).le
lemma primitive_separating_nonneg (P : PsiTheory) (g pivot : ℕ) (d : List ℤ) :
    0 ≤ ∑ u ∈ Finset.range (pivot-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        let c₁ := (u : ℤ) :: selected d I
        let c₂ := ((pivot : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)
        (Real.Gamma (complexity g₁ c₁.length) * Real.Gamma (complexity (g-g₁) c₂.length) /
          (6*Real.Gamma (complexity g (d.length+1)))) *
        signedPureC P g₁ c₁ * signedPureC P (g-g₁) c₂ := by
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro g₁ hg₁
  apply Finset.sum_nonneg
  intro I hI
  exact mul_nonneg (mul_nonneg
    (div_nonneg (mul_nonneg (gamma_nat_nonneg _) (gamma_nat_nonneg _))
      (mul_nonneg (by norm_num) (gamma_nat_nonneg _)))
    (signedPureC_nonneg P _ _)) (signedPureC_nonneg P _ _)
lemma sum_positive_string_weights (d : List ℤ) (hd : ∀ k ∈ d, 0 ≤ k) :
    (∑ j ∈ Finset.range d.length, if 0 < d[j]! then (2*(d[j]! : ℝ)+1) else 0) =
      2*(d.sum : ℝ)+d.length-d.count 0 := by
  induction d with
  | nil => simp
  | cons k d ih =>
    have hk := hd k (by simp)
    have ht : ∀ k ∈ d, 0 ≤ k := fun k hk => hd k (by simp [hk])
    simp only [List.length_cons, Finset.sum_range_succ', List.getElem!_cons_zero,
      List.getElem!_cons_succ, ih ht, List.sum_cons, Int.cast_add, Nat.cast_add,
      Nat.cast_one, List.count_cons]
    by_cases hz : k = 0
    · subst k; simp; ring
    · have hp : 0 < k := by omega
      simp only [hp, ite_true, beq_iff_eq, hz, ite_false, Nat.cast_zero]
      ring
lemma sum_linear_primitive_weights (g pivot : ℕ) (d : List ℤ)
    (hp : 1 ≤ pivot) (hh : 2 ≤ complexity g (d.length+1)) (hdim : ((pivot : ℤ) :: d).sum = 3*(g : ℤ)-3+(d.length+1)) :
    (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)) + 2*(pivot-1 : ℕ) =
      3*((complexity g (d.length+1) : ℝ)-1) := by
  have hsum : (∑ j ∈ Finset.range d.length, (d[j]! : ℝ)) = (d.sum : ℝ) := by
    clear hdim hh hp
    induction d with
    | nil => simp
    | cons k d ih =>
      simp only [List.length_cons, Finset.sum_range_succ', List.getElem!_cons_zero,
        List.getElem!_cons_succ, ih, List.sum_cons, Int.cast_add]
      ring
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hdimR : (pivot : ℝ)+(d.sum : ℝ) = 3*(g : ℝ)-3+(d.length+1) := by exact_mod_cast hdim
  have hc : (complexity g (d.length+1) : ℝ) = 2*(g : ℝ)+d.length-1 := by
    have hcast : 2 ≤ 2*g+(d.length+1) := by unfold complexity at hh; omega
    unfold complexity
    rw [Nat.cast_sub hcast]
    push_cast
    ring
  rw [hc, Nat.cast_sub hp]
  norm_num only [Nat.cast_one]
  linarith
lemma signedPrimitive_lower_positive_step (P : PsiTheory) (g pivot : ℕ) (d : List ℤ)
    (hg : 1 ≤ g) (hp : 1 ≤ pivot) (hd : ∀ k ∈ d, 0 ≤ k)
    (hh : 2 ≤ complexity g (d.length+1))
    (hdim : ((pivot : ℤ) :: d).sum = 3*(g : ℤ)-3+(d.length+1))
    (hm : ∀ j ∈ Finset.range d.length,
      (1/6 : ℝ) ≤ signedPureC P g (((pivot : ℤ)+d[j]!-1) :: d.eraseIdx j))
    (hn : ∀ u ∈ Finset.range (pivot-1),
      (1/6 : ℝ) ≤ signedPureC P (g-1) ((u : ℤ) :: ((pivot : ℤ)-2-u) :: d)) :
    (1/6 : ℝ) ≤ signedPureC P g ((pivot : ℤ) :: d) := by
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
    apply div_nonneg (by linarith) hden.le
  have hlinear := sum_linear_primitive_weights g pivot d hp hh hdim
  have he : (1/6 : ℝ) =
      (∑ j ∈ Finset.range d.length,
        ((2*(d[j]! : ℝ)+1)/(3*((complexity g (d.length+1) : ℝ)-1))) * (1/6)) +
      (2/(3*((complexity g (d.length+1) : ℝ)-1))) *
        ∑ u ∈ Finset.range (pivot-1), (1/6 : ℝ) := by
    simp only [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    field_simp [show (complexity g (d.length+1) : ℝ)-1 ≠ 0 by linarith]
    nlinarith [hlinear]
  rw [signedPureC_dvv P g pivot d hd hh]
  unfold primitiveDvvRHS
  rw [if_neg (by omega : g ≠ 0)]
  have hl :
      (∑ j ∈ Finset.range d.length,
        ((2*(d[j]! : ℝ)+1)/(3*((complexity g (d.length+1) : ℝ)-1))) * (1/6)) +
      (2/(3*((complexity g (d.length+1) : ℝ)-1))) *
        ∑ u ∈ Finset.range (pivot-1), (1/6 : ℝ) ≤
      (∑ j ∈ Finset.range d.length,
        ((2*(d[j]! : ℝ)+1)/(3*((complexity g (d.length+1) : ℝ)-1))) *
          signedPureC P g (((pivot : ℤ)+d[j]!-1) :: d.eraseIdx j)) +
      (2/(3*((complexity g (d.length+1) : ℝ)-1))) *
        ∑ u ∈ Finset.range (pivot-1),
          signedPureC P (g-1) ((u : ℤ) :: ((pivot : ℤ)-2-u) :: d) := by
    apply add_le_add
    · apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hm j hj) (hcoef j hj)
    · apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) hden.le)
      exact Finset.sum_le_sum hn
  exact he.le.trans (hl.trans (le_add_of_nonneg_right
    (primitive_separating_nonneg P g pivot d)))
lemma signedPrimitive_lower_zero_step (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hd : ∀ k ∈ d, 0 ≤ k) (hz : d.count 0 ≤ 1)
    (hh : 2 ≤ complexity g (d.length+1))
    (hdim : (0 :: d).sum = 3*(g : ℤ)-3+(d.length+1))
    (hm : ∀ j ∈ Finset.range d.length, 0 < d[j]! →
      (1/6 : ℝ) ≤ signedPureC P g ((d[j]!-1) :: d.eraseIdx j)) :
    (1/6 : ℝ) ≤ signedPureC P g (0 :: d) := by
  have hhR : (2 : ℝ) ≤ complexity g (d.length+1) := by exact_mod_cast hh
  have hden : (0 : ℝ) < 3*((complexity g (d.length+1) : ℝ)-1) := by linarith
  have hweights := sum_positive_string_weights d hd
  have hdimR : (d.sum : ℝ) = 3*(g : ℝ)-3+(d.length+1) := by
    simp only [List.sum_cons, zero_add] at hdim
    exact_mod_cast hdim
  have hc : (complexity g (d.length+1) : ℝ) = 2*(g : ℝ)+d.length-1 := by
    unfold complexity at hh ⊢
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hzR : (d.count 0 : ℝ) ≤ 1 := by exact_mod_cast hz
  have hsum : 3*((complexity g (d.length+1) : ℝ)-1) ≤
      ∑ j ∈ Finset.range d.length, if 0 < d[j]! then (2*(d[j]! : ℝ)+1) else 0 := by
    rw [hweights,hc]
    linarith
  have hsum' : (1/6 : ℝ) ≤
      ((∑ j ∈ Finset.range d.length, if 0 < d[j]! then (2*(d[j]! : ℝ)+1) else 0) /
        (3*((complexity g (d.length+1) : ℝ)-1))) * (1/6) := by
    have hw : (1 : ℝ) ≤ _ / (3*((complexity g (d.length+1) : ℝ)-1)) :=
      (one_le_div hden).mpr hsum
    linarith
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
    signedPureC_dvv P g 0 d hd hh]
  simp only [primitiveDvvRHS, Nat.zero_sub, Finset.range_zero, Finset.sum_empty,
    mul_zero, ite_self, add_zero, Int.natCast_zero, zero_add]
  apply hsum'.trans
  rw [Finset.sum_div, Finset.sum_mul]
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
    simp only [zero_div, zero_mul]
    exact mul_nonneg hcoef (signedPureC_nonneg P g _)
lemma twice_length_le_sum (d : List ℤ) (hd : ∀ k ∈ d, 2 ≤ k) :
    2*(d.length : ℤ) ≤ d.sum := by
  induction d with
  | nil => simp
  | cons k d ih =>
    have hk := hd k (by simp)
    have hh := ih (fun k hk => hd k (by simp [hk]))
    simp only [List.length_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    omega
lemma signedPrimitive_lower_aux (P : PsiTheory) (h : ℕ) :
    ∀ g : ℕ, ∀ d : List ℤ, 1 ≤ g → Stable g d.length →
      (∀ k ∈ d, 0 ≤ k) → d.count 0 ≤ 2 →
      d.sum = 3*(g : ℤ)-3+d.length → complexity g d.length = h →
      (1/6 : ℝ) ≤ signedPureC P g d := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro g d hg hst hd hz hdim he
    by_cases hs : h ≤ 1
    · have hc : g = 1 ∧ d.length = 1 := by
        unfold Stable at hst
        unfold complexity at he
        omega
      obtain ⟨rfl,hn⟩ := hc
      obtain ⟨p,rfl⟩ := List.length_eq_one_iff.mp hn
      have hp : p = 1 := by simpa using hdim
      subst p
      norm_num [signedPureC,primitiveScale,weighted,doubleWeight,complexity,
        oddFactorial,Finset.prod_range_succ,P.base₁]
    · have hlarge : 2 ≤ h := by omega
      by_cases hzero : (0 : ℤ) ∈ d
      · let t := d.erase 0
        have hp : d.Perm (0 :: t) := List.perm_cons_erase hzero
        have hl : d.length = t.length+1 := by simpa using hp.length_eq
        have ht : ∀ k ∈ t, 0 ≤ k := fun k hk => hd k (List.mem_of_mem_erase hk)
        have hdim' : (0 :: t).sum = 3*(g : ℤ)-3+(t.length+1) := by
          rw [← hp.sum_eq]
          simpa only [hl,Nat.cast_add,Nat.cast_one] using hdim
        have hh : 2 ≤ complexity g (t.length+1) := by rw [← hl,he]; exact hlarge
        have hzt : t.count 0 ≤ 1 := by
          have hcount := hp.count_eq 0
          simp only [List.count_cons,beq_self_eq_true,ite_true] at hcount
          omega
        rw [signedPureC_perm P g hp]
        apply signedPrimitive_lower_zero_step P g t ht hzt hh hdim'
        intro j hj hjpos
        have hj' := Finset.mem_range.mp hj
        let c := (t[j]!-1) :: t.eraseIdx j
        have hlen : c.length = t.length := by
          dsimp only [c]
          simp only [List.length_cons,List.length_eraseIdx_of_lt hj']
          omega
        have hc : complexity g c.length < h := by
          rw [hlen]
          unfold complexity at he ⊢
          rw [hl] at he
          omega
        apply ih _ hc g c hg
        · unfold Stable
          rw [hlen]
          unfold complexity at hh
          omega
        · intro k hk
          rcases List.mem_cons.mp hk with hk | hk
          · subst k; omega
          · exact ht k (List.mem_of_mem_eraseIdx hk)
        · have hper := List.getElem_cons_eraseIdx_perm hj'
          have hec := hper.count_eq 0
          have hj0 : t[j] ≠ (0 : ℤ) := by simpa [hj'] using ne_of_gt hjpos
          simp only [List.count_cons,beq_iff_eq,hj0,ite_false,add_zero] at hec
          dsimp only [c]
          simp only [List.count_cons]
          split_ifs <;> omega
        · simpa only [c,zero_add] using merger_dimension g 0 t hdim' j hj'
        · rfl
      · by_cases hone : (1 : ℤ) ∈ d
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
          have hchild : complexity g t.length < h := by
            unfold complexity at he ⊢
            rw [hl] at he
            omega
          have hst' : Stable g t.length := by
            unfold Stable
            unfold complexity at he
            rw [hl] at he
            omega
          rw [signedPureC_perm P g hp,signedPureC_dilaton P g t hst']
          exact ih _ hchild g t hg hst' ht
            (le_trans (List.Sublist.count_le 0 (List.erase_sublist)) hz) hdim' rfl
        · have hd₂ : ∀ k ∈ d, 2 ≤ k := by
            intro k hk
            have hk0 := hd k hk
            have hkz : k ≠ 0 := fun h => hzero (h ▸ hk)
            have hk1 : k ≠ 1 := fun h => hone (h ▸ hk)
            omega
          have hg₂ : 2 ≤ g := by
            have hsum := twice_length_le_sum d hd₂
            unfold Stable at hst
            omega
          cases d with
          | nil => simp only [List.length_nil,List.sum_nil,Nat.cast_zero] at hdim; omega
          | cons p t =>
            have hp := hd₂ p (by simp)
            have ht : ∀ k ∈ t, 2 ≤ k := fun k hk => hd₂ k (by simp [hk])
            have hpN : 2 ≤ p.toNat := by omega
            have hcast : ((p.toNat : ℕ) : ℤ) = p := Int.toNat_of_nonneg (by omega)
            have hh : 2 ≤ complexity g (t.length+1) := by simpa only [List.length_cons] using he ▸ hlarge
            have hdim' : ((p.toNat : ℤ) :: t).sum = 3*(g : ℤ)-3+(t.length+1) := by
              simpa only [hcast,List.length_cons,Nat.cast_add,Nat.cast_one] using hdim
            rw [← hcast]
            apply signedPrimitive_lower_positive_step P g p.toNat t hg (by omega)
              (fun k hk => le_trans (by norm_num) (ht k hk)) hh hdim'
            · intro j hj
              have hj' := Finset.mem_range.mp hj
              have hval : 2 ≤ t[j]! := by
                apply ht
                simpa [hj'] using (List.getElem_mem (l := t) j hj')
              let c := ((p.toNat : ℤ)+t[j]!-1) :: t.eraseIdx j
              have hlen : c.length = t.length := by
                dsimp only [c]
                simp only [List.length_cons,List.length_eraseIdx_of_lt hj']
                omega
              have hc : complexity g c.length < h := by
                rw [hlen]
                unfold complexity at he ⊢
                simp only [List.length_cons] at he
                omega
              have hcp : ∀ k ∈ c, 0 < k := by
                intro k hk
                rcases List.mem_cons.mp hk with hk | hk
                · subst k; omega
                · have := ht k (List.mem_of_mem_eraseIdx hk); omega
              apply ih _ hc g c hg
              · unfold Stable
                rw [hlen]
                omega
              · exact fun k hk => (hcp k hk).le
              · have hz' : c.count 0 = 0 := List.count_eq_zero.mpr
                  (fun hm => by have := hcp 0 hm; omega)
                omega
              · exact merger_dimension g p.toNat t hdim' j hj'
              · rfl
            · intro u hu
              have hu' := Finset.mem_range.mp hu
              let c := (u : ℤ) :: ((p.toNat : ℤ)-2-u) :: t
              have hc : complexity (g-1) c.length < h := by
                dsimp only [c]
                unfold complexity at he ⊢
                simp only [List.length_cons] at he ⊢
                omega
              have hzt : t.count 0 = 0 := List.count_eq_zero.mpr
                (fun hm => by have := ht 0 hm; omega)
              apply ih _ hc (g-1) c (by omega)
              · unfold Stable
                dsimp only [c]
                simp only [List.length_cons]
                omega
              · intro k hk
                rcases List.mem_cons.mp hk with hk | hk
                · subst k; positivity
                · rcases List.mem_cons.mp hk with hk | hk
                  · subst k; omega
                  · have := ht k hk; omega
              · dsimp only [c]
                simp only [List.count_cons,hzt]
                split_ifs <;> omega
              · exact contraction_dimension g (by omega) p.toNat t hdim' u
              · rfl
lemma pureC_primitive_lower (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hg : 1 ≤ g) (hn : 1 ≤ d.length) (hd : ∀ k ∈ d, 0 < k)
    (hdim : d.sum = dimension g d.length) : (1/6 : ℝ) ≤ pureC P g d := by
  have hs : Stable g d.length := by unfold Stable; omega
  have hd' : ∀ k ∈ d.map Int.ofNat, 0 < k := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
    change (0 : ℤ) < (j : ℤ)
    exact_mod_cast hd j hj
  rw [pureC_signed]
  apply signedPrimitive_lower_aux P (complexity g (d.map Int.ofNat).length)
    g (d.map Int.ofNat) hg
  · simpa only [List.length_map] using hs
  · exact fun k hk => (hd' k hk).le
  · have hz : (d.map Int.ofNat).count 0 = 0 := List.count_eq_zero.mpr
      (fun hm => by have := hd' 0 hm; omega)
    omega
  · rw [sum_map_int,hdim,List.length_map]
    exact dimension_cast_of_stable g d.length hs
  · rfl
end WP
