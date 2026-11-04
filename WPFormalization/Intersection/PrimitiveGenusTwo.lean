import WPFormalization.Intersection.PrimitiveLower
import WPFormalization.Intersection.PrimitiveIdentities
/-! Exact genus-two core values from the actual DVV and string equations,
followed by the complete positive-genus-two upper estimate by dilaton and finite
core classification. No external one- or two-point estimate is used. -/
noncomputable section
namespace WP
lemma psi_unstable (P : PsiTheory) (g : ℕ) (d : List ℤ) (hs : ¬ Stable g d.length) :
    P.psi g d = 0 := P.vanish g d (Or.inl hs)
lemma psi_1_1_1 (P : PsiTheory) : P.psi 1 [1,1] = 1/24 := by
  have h := P.dilaton 1 [1] (by norm_num [Stable])
  norm_num [P.base₁] at h
  exact h
lemma psi_1_0_0_3 (P : PsiTheory) : P.psi 1 [0,0,3] = 1/24 := by
  have h := P.string 1 [0,3] (by norm_num [Stable])
  have hn := P.vanish 1 [-1,3] (Or.inr (Or.inl ⟨-1,by simp,by norm_num⟩))
  norm_num [Finset.sum_range_succ,hn,psi_1_0_2] at h
  exact h
lemma psi_1_0_1_2 (P : PsiTheory) : P.psi 1 [0,1,2] = 1/12 := by
  have h := P.string 1 [1,2] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_1_0_2,psi_1_1_1] at h
  exact h
lemma psi_1_0_2_1 (P : PsiTheory) : P.psi 1 [0,2,1] = 1/12 := by
  have h := P.symmetry 1 [0,2,1] [0,1,2]
    (List.Perm.cons 0 (List.Perm.swap (1 : ℤ) 2 []))
  rw [h,psi_1_0_1_2]
lemma psi_1_0_0_2_2 (P : PsiTheory) : P.psi 1 [0,0,2,2] = 1/6 := by
  have h := P.string 1 [0,2,2] (by norm_num [Stable])
  have hn := P.vanish 1 [-1,2,2] (Or.inr (Or.inl ⟨-1,by simp,by norm_num⟩))
  norm_num [Finset.sum_range_succ,hn,psi_1_0_1_2,psi_1_0_2_1] at h
  exact h
lemma psi_dimension (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hd : d.sum ≠ 3*(g : ℤ)-3+d.length) : P.psi g d = 0 :=
  P.vanish g d (Or.inr (Or.inr hd))
lemma psi_1_2_0 (P : PsiTheory) : P.psi 1 [2,0] = 1/24 := by
  rw [P.symmetry 1 [2,0] [0,2] (List.Perm.swap (0 : ℤ) 2 []),psi_1_0_2]
lemma psi_2_4 (P : PsiTheory) : P.psi 2 [4] = 1/1152 := by
  have h := P.dvv 2 4 [] (by simp) (by norm_num [complexity])
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,Finset.sum_insert,List.range_succ,selected,psi_1_0_2,psi_1_1_1,psi_1_2_0,
    psi_unstable,Stable,psi_dimension,P.base₁] at h
  linarith
lemma psi_2_2_3 (P : PsiTheory) : P.psi 2 [2,3] = 29/5760 := by
  have h := P.dvv 2 2 [3] (by norm_num) (by norm_num [complexity])
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,Finset.sum_insert,List.range_succ,selected,psi_2_4,psi_1_0_0_3,
    psi_unstable,Stable,psi_dimension] at h
  linarith
lemma psi_2_3_2 (P : PsiTheory) : P.psi 2 [3,2] = 29/5760 := by
  rw [P.symmetry 2 [3,2] [2,3] (List.Perm.swap (2 : ℤ) 3 []),psi_2_2_3]
lemma psi_2_2_2_2 (P : PsiTheory) : P.psi 2 [2,2,2] = 7/240 := by
  have h := P.dvv 2 2 [2,2] (by norm_num) (by norm_num [complexity])
  have hpow : (Finset.range 2).powerset = {∅,{0},{1},{0,1}} := by decide
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,Finset.sum_insert,List.range_succ,selected,psi_2_3_2,psi_1_0_0_2_2,
    psi_1_0_2,psi_unstable,Stable,psi_dimension,hpow,
    show ({0} : Finset ℕ) ≠ {1} from by decide,
    show ({0} : Finset ℕ) ≠ {0,1} from by decide,
    show ({1} : Finset ℕ) ≠ {0,1} from by decide] at h
  linarith
lemma pureC_genus_two_four (P : PsiTheory) : pureC P 2 [4] = 35/144 := by
  norm_num [pureC,pure,complexity,oddFactorial,Finset.prod_range_succ,psi_2_4]
lemma pureC_genus_two_two_three (P : PsiTheory) : pureC P 2 [2,3] = 1015/3888 := by
  norm_num [pureC,pure,complexity,oddFactorial,Finset.prod_range_succ,psi_2_2_3]
lemma pureC_genus_two_two_two_two (P : PsiTheory) : pureC P 2 [2,2,2] = 175/648 := by
  norm_num [pureC,pure,complexity,oddFactorial,Finset.prod_range_succ,psi_2_2_2_2]
lemma pureC_perm (P : PsiTheory) (g : ℕ) {d e : List ℕ} (hp : d.Perm e) :
    pureC P g d = pureC P g e := by
  rw [pureC_signed,pureC_signed]
  exact signedPureC_perm P g (hp.map Int.ofNat)
lemma twice_length_le_sum_nat (d : List ℕ) (hd : ∀ k ∈ d, 2 ≤ k) :
    2*d.length ≤ d.sum := by
  induction d with
  | nil => simp
  | cons k d ih =>
    have hk := hd k (by simp)
    have hh := ih (fun k hk => hd k (by simp [hk]))
    simp only [List.length_cons,List.sum_cons]
    omega
lemma pureC_genus_two_aux (P : PsiTheory) (n : ℕ) :
    ∀ d : List ℕ, d.length = n → (∀ k ∈ d, 0 < k) →
      d.sum = dimension 2 d.length → pureC P 2 d < 3/11 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro d he hd hdim
    by_cases hone : (1 : ℕ) ∈ d
    · let t := d.erase 1
      have hp : d.Perm (1 :: t) := List.perm_cons_erase hone
      have hl : d.length = t.length+1 := by simpa using hp.length_eq
      have ht : ∀ k ∈ t, 0 < k := fun k hk => hd k (List.mem_of_mem_erase hk)
      have hdim' : t.sum = dimension 2 t.length := by
        have hh := hp.sum_eq
        simp only [List.sum_cons] at hh
        unfold dimension at hdim ⊢
        omega
      rw [pureC_perm P 2 hp,pureC_dilaton P 2 t (by unfold Stable; omega)]
      exact ih t.length (by omega) t rfl ht hdim'
    · have hd₂ : ∀ k ∈ d, 2 ≤ k := by
        intro k hk
        have hpos := hd k hk
        have hk1 : k ≠ 1 := fun h => hone (h ▸ hk)
        omega
      have hlen : d.length ≤ 3 := by
        have hs := twice_length_le_sum_nat d hd₂
        unfold dimension at hdim
        omega
      cases d with
      | nil => norm_num [dimension] at hdim
      | cons a t =>
        have ha := hd₂ a (by simp)
        cases t with
        | nil =>
          have hea : a = 4 := by simpa [dimension] using hdim
          subst a
          rw [pureC_genus_two_four]
          norm_num
        | cons b t =>
          have hb := hd₂ b (by simp)
          cases t with
          | nil =>
            have hab : a+b = 5 := by simpa [dimension] using hdim
            have hab' : (a=2 ∧ b=3) ∨ (a=3 ∧ b=2) := by omega
            rcases hab' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
            · rw [pureC_genus_two_two_three]; norm_num
            · rw [pureC_perm P 2 (List.Perm.swap (2 : ℕ) 3 []),
                pureC_genus_two_two_three]; norm_num
          | cons c t =>
            have hc := hd₂ c (by simp)
            have ht0 : t = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
            subst t
            have habc : a+b+c = 6 := by simpa [dimension,add_assoc] using hdim
            have hea : a=2 := by omega
            have heb : b=2 := by omega
            have hec : c=2 := by omega
            subst a; subst b; subst c
            rw [pureC_genus_two_two_two_two]
            norm_num
lemma pureC_genus_two_lt (P : PsiTheory) (d : List ℕ)
    (hd : ∀ k ∈ d, 0 < k) (hdim : d.sum = dimension 2 d.length) :
    pureC P 2 d < 3/11 := pureC_genus_two_aux P d.length d rfl hd hdim
end WP
