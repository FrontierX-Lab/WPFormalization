import WPFormalization.Intersection.BackgroundMerging
import WPFormalization.Intersection.TopDegree
/-! Positivity of the actual classical numerical interface, derived from DVV by
strong induction in the stable complexity. No positivity field is assumed. -/
noncomputable section
namespace WP
lemma eq_replicate_zero_of_nonneg_sum (d : List ℤ) (hd : ∀ k ∈ d, 0 ≤ k)
    (hs : d.sum = 0) : d = List.replicate d.length 0 := by
  induction d with
  | nil => rfl
  | cons a d ih =>
    have ha := hd a (by simp)
    have ht : ∀ k ∈ d, 0 ≤ k := fun k hk => hd k (by simp [hk])
    have hsum := List.sum_nonneg ht
    simp only [List.sum_cons] at hs
    have ha0 : a = 0 := by omega
    have hs0 : d.sum = 0 := by omega
    subst a
    simpa only [List.length_cons, List.replicate_succ] using congrArg (List.cons 0) (ih ht hs0)
lemma weighted_nonneg_aux (P : PsiTheory) (h : ℕ) :
    ∀ g : ℕ, ∀ d : List ℤ, complexity g d.length = h → 0 ≤ weighted P.psi g d := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro g d he
    by_cases hst : Stable g d.length
    · by_cases hd : ∀ k ∈ d, 0 ≤ k
      · by_cases hdim : d.sum = 3*(g : ℤ)-3+d.length
        · by_cases hsmall : h ≤ 1
          · have hc : (g = 0 ∧ d.length = 3) ∨ (g = 1 ∧ d.length = 1) := by
              unfold complexity at he
              unfold Stable at hst
              omega
            rcases hc with ⟨rfl, hn⟩ | ⟨rfl, hn⟩
            · have hs : d.sum = 0 := by rw [hn] at hdim; norm_num at hdim; exact hdim
              have ht := eq_replicate_zero_of_nonneg_sum d hd hs
              rw [hn] at ht
              rw [ht]
              norm_num [weighted, doubleWeight, oddFactorial, Finset.prod_range_succ, P.base₀]
            · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hn
              have ha : a = 1 := by simpa using hdim
              rw [ha]
              norm_num [weighted, doubleWeight, oddFactorial, Finset.prod_range_succ, P.base₁]
          · have hlarge : 2 ≤ h := by omega
            cases d with
            | nil =>
              simp only [Stable, List.length_nil] at hst
              simp only [List.sum_nil, List.length_nil, Nat.cast_zero] at hdim
              omega
            | cons p d =>
              have hp : 0 ≤ p := hd p (by simp)
              have hdt : ∀ k ∈ d, 0 ≤ k := fun k hk => hd k (by simp [hk])
              change 2*g+(d.length+1)-2 = h at he
              have hv := P.dvv g p.toNat d hdt (by unfold complexity; omega)
              rw [Int.toNat_of_nonneg hp] at hv
              rw [hv]
              unfold dvvRHS
              apply add_nonneg
              · apply add_nonneg
                · apply Finset.sum_nonneg
                  intro j hj
                  have hj' := Finset.mem_range.mp hj
                  have hval : 0 ≤ d[j]! := by
                    apply hdt
                    simpa [hj'] using (List.getElem_mem (l := d) j hj')
                  have hcoef : 0 ≤ 2*(d[j]! : ℝ)+1 := by
                    have hh0 : (0 : ℝ) ≤ (d[j]! : ℝ) := by exact_mod_cast hval
                    linarith
                  apply mul_nonneg hcoef
                  let c : List ℤ := ((p.toNat : ℤ)+d[j]!-1) :: d.eraseIdx j
                  have hc : complexity g c.length < h := by
                    dsimp only [c]
                    simp only [List.length_cons, List.length_eraseIdx_of_lt hj']
                    unfold complexity
                    omega
                  exact ih _ hc g c rfl
                · by_cases hg : g = 0
                  · simp [hg]
                  · simp only [hg, ite_false]
                    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)
                    apply Finset.sum_nonneg
                    intro u hu
                    let c : List ℤ := (u : ℤ) :: ((p.toNat : ℤ)-2-u) :: d
                    have hc : complexity (g-1) c.length < h := by
                      dsimp only [c]
                      simp only [List.length_cons]
                      unfold complexity
                      omega
                    exact ih _ hc (g-1) c rfl
              · apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)
                apply Finset.sum_nonneg
                intro u hu
                apply Finset.sum_nonneg
                intro g₁ hg₁
                apply Finset.sum_nonneg
                intro I hI
                let c₁ : List ℤ := (u : ℤ) :: selected d I
                let c₂ : List ℤ := ((p.toNat : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)
                by_cases hs₁ : Stable g₁ c₁.length
                · by_cases hs₂ : Stable (g-g₁) c₂.length
                  · have hg₁' : g₁ ≤ g := by have := Finset.mem_range.mp hg₁; omega
                    have hpart := selected_partition_length d I
                    have hc₁ : complexity g₁ c₁.length < h := by
                      dsimp only [c₁]
                      simp only [List.length_cons]
                      unfold complexity
                      dsimp only [c₁, c₂] at hs₁ hs₂
                      simp only [Stable, List.length_cons] at hs₁ hs₂
                      omega
                    have hc₂ : complexity (g-g₁) c₂.length < h := by
                      dsimp only [c₂]
                      simp only [List.length_cons]
                      unfold complexity
                      dsimp only [c₁, c₂] at hs₁ hs₂
                      simp only [Stable, List.length_cons] at hs₁ hs₂
                      omega
                    exact mul_nonneg (ih _ hc₁ g₁ c₁ rfl) (ih _ hc₂ (g-g₁) c₂ rfl)
                  · have hz := P.vanish (g-g₁) c₂ (Or.inl hs₂)
                    change 0 ≤ weighted P.psi g₁ c₁ * weighted P.psi (g-g₁) c₂
                    simp only [weighted, hz, mul_zero, le_refl]
                · have hz := P.vanish g₁ c₁ (Or.inl hs₁)
                  change 0 ≤ weighted P.psi g₁ c₁ * weighted P.psi (g-g₁) c₂
                  simp only [weighted, hz, mul_zero, zero_mul, le_refl]
        · have hz := P.vanish g d (Or.inr (Or.inr hdim))
          simp [weighted, hz]
      · have hneg : ∃ k ∈ d, k < 0 := by push Not at hd; exact hd
        have hz := P.vanish g d (Or.inr (Or.inl hneg))
        simp [weighted, hz]
    · have hz := P.vanish g d (Or.inl hst)
      simp [weighted, hz]
lemma weighted_nonneg (P : PsiTheory) (g : ℕ) (d : List ℤ) : 0 ≤ weighted P.psi g d :=
  weighted_nonneg_aux P (complexity g d.length) g d rfl
lemma psi_nonneg (P : PsiTheory) (g : ℕ) (d : List ℤ) : 0 ≤ P.psi g d := by
  have he := weighted_nonneg P g d
  unfold weighted at he
  exact nonneg_of_mul_nonneg_right he (doubleWeight_pos d)
end WP
