import WPFormalization.Statements.IntersectionInterface

/-! Finite combinatorics of the classical psi interface. Every theorem in this file
is proved from the explicitly listed `PsiTheory` fields, without additional axioms. -/
noncomputable section
namespace WP

lemma psi_negative_entry (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (h : ∃ k ∈ d, k < 0) : P.psi g d = 0 :=
  P.vanish g d (Or.inr (Or.inl h))

lemma psi_set_negative (P : PsiTheory) (g : ℕ) (d : List ℤ) (j : ℕ)
    (hj : j < d.length) : P.psi g (d.set j (-1)) = 0 := by
  apply psi_negative_entry
  exact ⟨-1, List.mem_set hj (-1), by norm_num⟩

lemma pure_perm (P : PsiTheory) (g : ℕ) {d e : List ℕ} (h : d.Perm e) :
    pure P g d = pure P g e :=
  P.symmetry g _ _ (h.map _)

lemma psi_zeros_twos_step (P : PsiTheory) (g p m : ℕ) (hg : 2 ≤ g) :
    P.psi g (List.replicate (p+1) 0 ++ List.replicate (m+1) 2) =
      (m+1 : ℝ) * (2*(g : ℝ)-2+p+m) *
        P.psi g (List.replicate p 0 ++ List.replicate m 2) := by
  let d : List ℤ := List.replicate p 0 ++ List.replicate (m+1) 2
  have hdlen : d.length = p + (m+1) := by simp [d]
  have hst : Stable g d.length := by simp only [Stable]; omega
  have hs := P.string g d hst
  have hleft : 0 :: d = List.replicate (p+1) 0 ++ List.replicate (m+1) 2 := by
    simp [d, List.replicate_succ]
  rw [hleft, hdlen, Finset.sum_range_add] at hs
  have hz : ∑ j ∈ Finset.range p, P.psi g (d.set j (d[j]!-1)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjp : j < p := Finset.mem_range.mp hj
    have hget : d[j]! = 0 := by
      apply List.getElem!_of_getElem?
      change (List.replicate p (0 : ℤ) ++ List.replicate (m+1) 2)[j]? = some 0
      rw [List.getElem?_append_left (by simpa using hjp)]
      simp [List.getElem?_replicate, hjp]
    rw [hget]
    norm_num
    exact psi_set_negative P g d j (by omega)
  rw [hz, zero_add] at hs
  have hmterm : ∀ j ∈ Finset.range (m+1),
      P.psi g (d.set (p+j) (d[p+j]!-1)) =
        (2*(g : ℝ)-2+p+m) * P.psi g (List.replicate p 0 ++ List.replicate m 2) := by
    intro j hj
    have hjm : j < m+1 := Finset.mem_range.mp hj
    have hidx : p+j < d.length := by omega
    have hget : d[p+j]! = 2 := by
      apply List.getElem!_of_getElem?
      change (List.replicate p (0 : ℤ) ++ List.replicate (m+1) 2)[p+j]? = some 2
      rw [List.getElem?_append_right (by simp)]
      simp [List.getElem?_replicate, hjm]
    have herase : d.eraseIdx (p+j) = List.replicate p 0 ++ List.replicate m 2 := by
      rw [List.eraseIdx_append_of_length_le (by simp)]
      simp [d, List.eraseIdx_replicate, hjm]
    have hp := List.set_perm_cons_eraseIdx hidx (1 : ℤ)
    rw [hget]
    norm_num
    rw [P.symmetry g _ _ hp, herase, P.dilaton]
    · simp only [List.length_append, List.length_replicate, Nat.cast_add]
      ring
    · simp only [Stable, List.length_append, List.length_replicate]
      omega
  rw [Finset.sum_congr rfl hmterm] at hs
  simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc] using hs

lemma pureC_zeros_twos_formula (P : PsiTheory) (g p m : ℕ) :
    pureC P g (List.replicate p 0 ++ List.replicate m 2) =
      (4 : ℝ)^g * 15^m /
        (3^(complexity g (p+m))*Real.Gamma (complexity g (p+m))) *
        P.psi g (List.replicate p 0 ++ List.replicate m 2) := by
  norm_num [pureC, pure, List.map_append, List.map_replicate,
    List.prod_append, List.prod_replicate, oddFactorial, Finset.prod_range_succ]

lemma pureC_zeros_twos_step (P : PsiTheory) (g p m : ℕ) (hg : 2 ≤ g) :
    pureC P g (List.replicate (p+1) 0 ++ List.replicate (m+1) 2) =
      5*(m+1 : ℝ)/(3*(2*(g : ℝ)-1+p+m)) *
        pureC P g (List.replicate p 0 ++ List.replicate m 2) := by
  rw [pureC_zeros_twos_formula, pureC_zeros_twos_formula,
    psi_zeros_twos_step P g p m hg]
  let h := complexity g (p+m)
  have hh : 2 ≤ h := by dsimp [h, complexity]; omega
  have he : complexity g (p+1+(m+1)) = h+2 := by dsimp [h, complexity]; omega
  have hr : (h : ℝ) = 2*(g : ℝ)-2+p+m := by
    dsimp [h, complexity]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [he]
  change _ = 5*(m+1 : ℝ)/(3*(2*(g : ℝ)-1+p+m)) *
    ((4 : ℝ)^g*15^m/(3^h*Real.Gamma h)*
      P.psi g (List.replicate p 0 ++ List.replicate m 2))
  have hne : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have hne' : (h : ℝ)+1 ≠ 0 := by positivity
  have hgamma : Real.Gamma (h+2 : ℕ) =
      ((h : ℝ)+1)*(h : ℝ)*Real.Gamma h := by
    norm_cast
    push_cast
    rw [show (h : ℝ)+2 = ((h : ℝ)+1)+1 by ring,
      Real.Gamma_add_one hne', Real.Gamma_add_one hne]
    ring
  rw [hgamma]
  have hden : 2*(g : ℝ)-1+p+m ≠ 0 := by have := hr; nlinarith [show 0 < (h : ℝ) by positivity]
  have hG : Real.Gamma h ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have heq : 2*(g : ℝ)-1+p+m = (h : ℝ)+1 := by linarith [hr]
  rw [heq, ← hr, pow_succ, pow_add]
  norm_num
  field_simp
  ring

lemma pureC_zeros_twos_reduce (P : PsiTheory) (g p q : ℕ) (hg : 2 ≤ g) (hpq : p ≤ q) :
    pureC P g (List.replicate p 0 ++ List.replicate q 2) =
      (∏ i ∈ Finset.range p, 5*((q : ℝ)-i) /
        (3*(2*(g : ℝ)-3+p+q-2*i))) *
        pureC P g (List.replicate (q-p) 2) := by
  induction p generalizing q with
  | zero => simp
  | succ p ih =>
    have hq : 1 ≤ q := by omega
    have hqeq : q = (q-1)+1 := by omega
    have hsub : q-1-p = q-(p+1) := by omega
    have hstep := pureC_zeros_twos_step P g p (q-1) hg
    rw [← hqeq] at hstep
    rw [hstep, ih (q-1) (by omega), hsub, Finset.prod_range_succ']
    have hr : ((q-1 : ℕ) : ℝ) = (q : ℝ)-1 := by
      simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hq)
    have hprod :
        (∏ k ∈ Finset.range p, 5*((q : ℝ)-(k+1)) /
          (3*(2*(g : ℝ)-3+(p+1)+q-2*(k+1)))) =
        ∏ k ∈ Finset.range p, 5*(((q-1 : ℕ) : ℝ)-k) /
          (3*(2*(g : ℝ)-3+p+(q-1 : ℕ)-2*k)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hr]
      congr 1 <;> ring
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, mul_zero] at *
    rw [hprod]
    rw [hr]
    have hcoeff :
        5*((q : ℝ)-1+1)/(3*(2*(g : ℝ)-1+p+((q : ℝ)-1))) =
        5*(q : ℝ)/(3*(2*(g : ℝ)-3+(p+1)+q)) := by ring
    rw [hcoeff]
    ring

end WP
