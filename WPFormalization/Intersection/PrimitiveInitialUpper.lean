import WPFormalization.Intersection.PrimitiveGenusThreeValues
import WPFormalization.Intersection.PrimitivePointBounds
/-! The complete finite initial-complexity upper estimate of Appendix B.
The proof combines exact genus-one/two/three cores with the registered
classical one- and two-point inputs for arbitrary genus and at most two
markings. Dilaton removes ones; the remaining initial core classification is
proved from positivity, dimension, and complexity at most seven. -/
noncomputable section
namespace WP
lemma pureC_at_most_two_lt (P : PsiTheory) (g : ℕ) (d : List ℕ) (hg : 1 ≤ g)
    (hn : 1 ≤ d.length) (hn₂ : d.length ≤ 2) (hdim : d.sum = dimension g d.length) :
    pureC P g d < 8/25 := by
  cases d with
  | nil => simp at hn
  | cons a t =>
    cases t with
    | nil =>
      have ha : a = 3*g-2 := by simpa [dimension] using hdim
      rw [ha]
      exact pureC_one_point_lt P g hg
    | cons b t =>
      have ht0 : t = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hn₂; omega)
      subst t
      have hab : a+b=3*g-1 := by simpa [dimension] using hdim
      exact pureC_two_point_lt P g a b hg hab
lemma primitive_initial_upper_aux (P : PsiTheory) (N : ℕ) :
    ∀ (g : ℕ) (d : List ℕ), 1 ≤ g → 1 ≤ d.length → d.length = N →
      (∀ k ∈ d, 0 < k) → d.sum = dimension g d.length → complexity g d.length ≤ 7 →
      pureC P g d ≤ 1/3 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro g d hg hn he hd hdim hh
    by_cases hg1 : g = 1
    · subst g
      rw [pureC_genus_one P d hn hd hdim]
      norm_num
    · have hg₂ : 2 ≤ g := by omega
      by_cases hg2 : g = 2
      · subst g
        exact (pureC_genus_two_lt P d hd hdim).le.trans (by norm_num)
      · have hg₃ : 3 ≤ g := by omega
        by_cases hsmall : d.length ≤ 2
        · exact (pureC_at_most_two_lt P g d hg hn hsmall hdim).le.trans (by norm_num)
        · by_cases hone : (1 : ℕ) ∈ d
          · let t := d.erase 1
            have hp : d.Perm (1 :: t) := List.perm_cons_erase hone
            have hl : d.length = t.length+1 := by simpa using hp.length_eq
            have ht : ∀ k ∈ t, 0 < k := fun k hk => hd k (List.mem_of_mem_erase hk)
            have hdim' : t.sum = dimension g t.length := by
              have hsum := hp.sum_eq
              simp only [List.sum_cons] at hsum
              unfold dimension at hdim ⊢
              omega
            have hst : Stable g t.length := by unfold Stable; omega
            have htlen : 1 ≤ t.length := by omega
            have hh' : complexity g t.length ≤ 7 := by unfold complexity at hh ⊢; omega
            rw [pureC_perm P g hp,pureC_dilaton P g t hst]
            exact ih t.length (by omega) g t hg htlen rfl ht hdim' hh'
          · have hg3 : g = 3 := by unfold complexity at hh; omega
            subst g
            have hn3 : d.length = 3 := by unfold complexity at hh; omega
            have hd₂ : ∀ k ∈ d, 2 ≤ k := by
              intro k hk
              have hkpos := hd k hk
              have hk1 : k ≠ 1 := fun h => hone (h ▸ hk)
              omega
            have hsum : d.sum = 9 := by simpa [dimension,hn3] using hdim
            by_cases htwo : (2 : ℕ) ∈ d
            · let t := d.erase 2
              have hp : d.Perm (2 :: t) := List.perm_cons_erase htwo
              have htlen : t.length = 2 := by have := hp.length_eq; simp only [List.length_cons] at this; omega
              obtain ⟨a,b,ht⟩ := List.length_eq_two.mp htlen
              have htpos : ∀ k ∈ t, 2 ≤ k := fun k hk => hd₂ k (List.mem_of_mem_erase hk)
              have ha := htpos a (by simp [ht])
              have hb := htpos b (by simp [ht])
              have hab : a+b=7 := by
                have heq := hp.sum_eq
                rw [hsum,ht] at heq
                simp only [List.sum_cons,List.sum_nil,add_zero] at heq
                omega
              rw [pureC_perm P 3 hp,ht]
              have hcases : (a=2 ∧ b=5) ∨ (a=3 ∧ b=4) ∨ (a=4 ∧ b=3) ∨ (a=5 ∧ b=2) := by omega
              rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
              · rw [pureC_genus_three_two_two_five]; norm_num
              · rw [pureC_genus_three_two_three_four]; norm_num
              · rw [pureC_perm P 3 (List.Perm.cons 2 (List.Perm.swap 3 4 [])),
                  pureC_genus_three_two_three_four]; norm_num
              · rw [pureC_perm P 3 (List.Perm.cons 2 (List.Perm.swap 2 5 [])),
                  pureC_genus_three_two_two_five]; norm_num
            · obtain ⟨a,b,c,rfl⟩ := List.length_eq_three.mp hn3
              have ha := hd₂ a (by simp)
              have hb := hd₂ b (by simp)
              have hc := hd₂ c (by simp)
              have ha2 : a ≠ 2 := fun h => htwo (by simp [h])
              have hb2 : b ≠ 2 := fun h => htwo (by simp [h])
              have hc2 : c ≠ 2 := fun h => htwo (by simp [h])
              simp only [List.sum_cons,List.sum_nil,add_zero] at hsum
              have hea : a = 3 := by omega
              have heb : b = 3 := by omega
              have hec : c = 3 := by omega
              subst a; subst b; subst c
              rw [pureC_genus_three_three_three_three]
              norm_num
lemma primitive_initial_upper (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hg : 1 ≤ g) (hn : 1 ≤ d.length) (hd : ∀ k ∈ d, 0 < k)
    (hdim : d.sum = dimension g d.length) (hh : complexity g d.length ≤ 7) :
    pureC P g d ≤ 1/3 :=
  primitive_initial_upper_aux P d.length g d hg hn rfl hd hdim hh
end WP
