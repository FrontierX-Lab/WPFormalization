import WPFormalization.Intersection.PrimitiveGenusTwo
/-! Exact finite genus-three core values for the initial cases of Appendix B.
Each private numerical lemma is proved from the original PsiTheory vanishing,
symmetry, string, dilaton, base, or weighted DVV field; the final norm_num steps
are rational arithmetic checked by Lean. No numerical oracle or deferred
intersection estimate is used. The three public core values imply the required
coarse bound 1/3. -/
noncomputable section
namespace WP
private lemma psi_finite_1_1 (P : PsiTheory) : P.psi 1 [1] = 1/24 := by
  exact P.base₁

private lemma psi_finite_1_0_2 (P : PsiTheory) : P.psi 1 [0,2] = 1/24 := by
  have h := P.string 1 [2] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_1_1] at h
  exact h

private lemma psi_finite_0_0 (P : PsiTheory) : P.psi 0 [0] = 0 := by
  exact P.vanish 0 [0] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_2_2 (P : PsiTheory) : P.psi 2 [2] = 0 := by
  exact P.vanish 2 [2] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_0 (P : PsiTheory) : P.psi 1 [0] = 0 := by
  exact P.vanish 1 [0] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_2 (P : PsiTheory) : P.psi 1 [2] = 0 := by
  exact P.vanish 1 [2] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_0 (P : PsiTheory) : P.psi 2 [0] = 0 := by
  exact P.vanish 2 [0] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_2 (P : PsiTheory) : P.psi 0 [2] = 0 := by
  exact P.vanish 0 [2] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_1_1_1 (P : PsiTheory) : P.psi 1 [1,1] = 1/24 := by
  have h := P.dilaton 1 [1] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_1_1] at h
  exact h

private lemma psi_finite_0_1 (P : PsiTheory) : P.psi 0 [1] = 0 := by
  exact P.vanish 0 [1] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_2_1 (P : PsiTheory) : P.psi 2 [1] = 0 := by
  exact P.vanish 2 [1] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_2_0 (P : PsiTheory) : P.psi 1 [2,0] = 1/24 := by
  rw [P.symmetry 1 [2,0] [0,2] (by decide),psi_finite_1_0_2]

private lemma psi_finite_2_4 (P : PsiTheory) : P.psi 2 [4] = 1/1152 := by
  have h := P.dvv 2 4 [] (by norm_num) (by norm_num [complexity])
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,Finset.sum_insert,List.range_succ,selected,
    show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,
    show (Finset.range 2).powerset = {∅,{0},{1},{0,1}} from by decide,
    show (∅ : Finset ℕ) ≠ {0} from by decide,
    show (∅ : Finset ℕ) ≠ {1} from by decide,
    show (∅ : Finset ℕ) ≠ {0,1} from by decide,
    show ({0} : Finset ℕ) ≠ {1} from by decide,
    show ({0} : Finset ℕ) ≠ {0,1} from by decide,
    show ({1} : Finset ℕ) ≠ {0,1} from by decide,
    psi_finite_1_0_2,
    psi_finite_0_0,
    psi_finite_2_2,
    psi_finite_1_0,
    psi_finite_1_2,
    psi_finite_2_0,
    psi_finite_0_2,
    psi_finite_1_1_1,
    psi_finite_0_1,
    psi_finite_2_1,
    psi_finite_1_1,
    psi_finite_1_2_0] at h
  linarith

private lemma psi_finite_2_0_5 (P : PsiTheory) : P.psi 2 [0,5] = 1/1152 := by
  have h := P.string 2 [5] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_2_4] at h
  exact h

private lemma psi_finite_3_5 (P : PsiTheory) : P.psi 3 [5] = 0 := by
  exact P.vanish 3 [5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_5 (P : PsiTheory) : P.psi 2 [5] = 0 := by
  exact P.vanish 2 [5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_5 (P : PsiTheory) : P.psi 1 [5] = 0 := by
  exact P.vanish 1 [5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_3_0 (P : PsiTheory) : P.psi 3 [0] = 0 := by
  exact P.vanish 3 [0] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_5 (P : PsiTheory) : P.psi 0 [5] = 0 := by
  exact P.vanish 0 [5] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_2_1_4 (P : PsiTheory) : P.psi 2 [1,4] = 1/384 := by
  have h := P.dilaton 2 [4] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_2_4] at h
  exact h

private lemma psi_finite_3_4 (P : PsiTheory) : P.psi 3 [4] = 0 := by
  exact P.vanish 3 [4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_4 (P : PsiTheory) : P.psi 1 [4] = 0 := by
  exact P.vanish 1 [4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_3_1 (P : PsiTheory) : P.psi 3 [1] = 0 := by
  exact P.vanish 3 [1] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_4 (P : PsiTheory) : P.psi 0 [4] = 0 := by
  exact P.vanish 0 [4] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_1_m1_3 (P : PsiTheory) : P.psi 1 [-1,3] = 0 := by
  exact P.vanish 1 [-1,3] (Or.inr (Or.inl ⟨-1,by simp,by norm_num⟩))

private lemma psi_finite_1_0_0_3 (P : PsiTheory) : P.psi 1 [0,0,3] = 1/24 := by
  have h := P.string 1 [0,3] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_1_m1_3,psi_finite_1_0_2] at h
  exact h

private lemma psi_finite_2_0_3 (P : PsiTheory) : P.psi 2 [0,3] = 0 := by
  exact P.vanish 2 [0,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_0_3 (P : PsiTheory) : P.psi 0 [0,3] = 0 := by
  exact P.vanish 0 [0,3] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_1_0_3 (P : PsiTheory) : P.psi 1 [0,3] = 0 := by
  exact P.vanish 1 [0,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_2_3 (P : PsiTheory) : P.psi 2 [2,3] = 29/5760 := by
  have h := P.dvv 2 2 [3] (by norm_num) (by norm_num [complexity])
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,Finset.sum_insert,List.range_succ,selected,
    show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,
    show (Finset.range 2).powerset = {∅,{0},{1},{0,1}} from by decide,
    show (∅ : Finset ℕ) ≠ {0} from by decide,
    show (∅ : Finset ℕ) ≠ {1} from by decide,
    show (∅ : Finset ℕ) ≠ {0,1} from by decide,
    show ({0} : Finset ℕ) ≠ {1} from by decide,
    show ({0} : Finset ℕ) ≠ {0,1} from by decide,
    show ({1} : Finset ℕ) ≠ {0,1} from by decide,
    psi_finite_2_4,
    psi_finite_1_0_0_3,
    psi_finite_0_0,
    psi_finite_2_0_3,
    psi_finite_0_0_3,
    psi_finite_2_0,
    psi_finite_1_0,
    psi_finite_1_0_3] at h
  linarith

private lemma psi_finite_3_3 (P : PsiTheory) : P.psi 3 [3] = 0 := by
  exact P.vanish 3 [3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_3 (P : PsiTheory) : P.psi 2 [3] = 0 := by
  exact P.vanish 2 [3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_3 (P : PsiTheory) : P.psi 1 [3] = 0 := by
  exact P.vanish 1 [3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_3_2 (P : PsiTheory) : P.psi 3 [2] = 0 := by
  exact P.vanish 3 [2] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_3 (P : PsiTheory) : P.psi 0 [3] = 0 := by
  exact P.vanish 0 [3] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_2_3_2 (P : PsiTheory) : P.psi 2 [3,2] = 29/5760 := by
  rw [P.symmetry 2 [3,2] [2,3] (by decide),psi_finite_2_2_3]

private lemma psi_finite_2_4_1 (P : PsiTheory) : P.psi 2 [4,1] = 1/384 := by
  rw [P.symmetry 2 [4,1] [1,4] (by decide),psi_finite_2_1_4]

private lemma psi_finite_2_5_0 (P : PsiTheory) : P.psi 2 [5,0] = 1/1152 := by
  rw [P.symmetry 2 [5,0] [0,5] (by decide),psi_finite_2_0_5]

private lemma psi_finite_3_7 (P : PsiTheory) : P.psi 3 [7] = 1/82944 := by
  have h := P.dvv 3 7 [] (by norm_num) (by norm_num [complexity])
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,Finset.sum_insert,List.range_succ,selected,
    show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,
    show (Finset.range 2).powerset = {∅,{0},{1},{0,1}} from by decide,
    show (∅ : Finset ℕ) ≠ {0} from by decide,
    show (∅ : Finset ℕ) ≠ {1} from by decide,
    show (∅ : Finset ℕ) ≠ {0,1} from by decide,
    show ({0} : Finset ℕ) ≠ {1} from by decide,
    show ({0} : Finset ℕ) ≠ {0,1} from by decide,
    show ({1} : Finset ℕ) ≠ {0,1} from by decide,
    psi_finite_2_0_5,
    psi_finite_0_0,
    psi_finite_3_5,
    psi_finite_1_0,
    psi_finite_2_5,
    psi_finite_2_0,
    psi_finite_1_5,
    psi_finite_3_0,
    psi_finite_0_5,
    psi_finite_2_1_4,
    psi_finite_0_1,
    psi_finite_3_4,
    psi_finite_1_1,
    psi_finite_2_4,
    psi_finite_2_1,
    psi_finite_1_4,
    psi_finite_3_1,
    psi_finite_0_4,
    psi_finite_2_2_3,
    psi_finite_0_2,
    psi_finite_3_3,
    psi_finite_1_2,
    psi_finite_2_3,
    psi_finite_2_2,
    psi_finite_1_3,
    psi_finite_3_2,
    psi_finite_0_3,
    psi_finite_2_3_2,
    psi_finite_2_4_1,
    psi_finite_2_5_0] at h
  linarith

private lemma psi_finite_2_0_1_5 (P : PsiTheory) : P.psi 2 [0,1,5] = 1/288 := by
  have h := P.string 2 [1,5] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_2_0_5,psi_finite_2_1_4] at h
  exact h

private lemma psi_finite_3_1_5 (P : PsiTheory) : P.psi 3 [1,5] = 0 := by
  exact P.vanish 3 [1,5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_0_5 (P : PsiTheory) : P.psi 0 [0,5] = 0 := by
  exact P.vanish 0 [0,5] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_2_1_5 (P : PsiTheory) : P.psi 2 [1,5] = 0 := by
  exact P.vanish 2 [1,5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_0_5 (P : PsiTheory) : P.psi 1 [0,5] = 0 := by
  exact P.vanish 1 [0,5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_1_5 (P : PsiTheory) : P.psi 1 [1,5] = 0 := by
  exact P.vanish 1 [1,5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_1_5 (P : PsiTheory) : P.psi 0 [1,5] = 0 := by
  exact P.vanish 0 [1,5] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_3_0_5 (P : PsiTheory) : P.psi 3 [0,5] = 0 := by
  exact P.vanish 3 [0,5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_1_0_5 (P : PsiTheory) : P.psi 2 [1,0,5] = 1/288 := by
  rw [P.symmetry 2 [1,0,5] [0,1,5] (by decide),psi_finite_2_0_1_5]

private lemma psi_finite_3_3_5 (P : PsiTheory) : P.psi 3 [3,5] = 503/1451520 := by
  have h := P.dvv 3 3 [5] (by norm_num) (by norm_num [complexity])
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,Finset.sum_insert,List.range_succ,selected,
    show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,
    show (Finset.range 2).powerset = {∅,{0},{1},{0,1}} from by decide,
    show (∅ : Finset ℕ) ≠ {0} from by decide,
    show (∅ : Finset ℕ) ≠ {1} from by decide,
    show (∅ : Finset ℕ) ≠ {0,1} from by decide,
    show ({0} : Finset ℕ) ≠ {1} from by decide,
    show ({0} : Finset ℕ) ≠ {0,1} from by decide,
    show ({1} : Finset ℕ) ≠ {0,1} from by decide,
    psi_finite_3_7,
    psi_finite_2_0_1_5,
    psi_finite_0_0,
    psi_finite_3_1_5,
    psi_finite_0_0_5,
    psi_finite_3_1,
    psi_finite_1_0,
    psi_finite_2_1_5,
    psi_finite_1_0_5,
    psi_finite_2_1,
    psi_finite_2_0,
    psi_finite_1_1_5,
    psi_finite_2_0_5,
    psi_finite_1_1,
    psi_finite_3_0,
    psi_finite_0_1_5,
    psi_finite_3_0_5,
    psi_finite_0_1,
    psi_finite_2_1_0_5] at h
  linarith

private lemma psi_finite_2_m1_6 (P : PsiTheory) : P.psi 2 [-1,6] = 0 := by
  exact P.vanish 2 [-1,6] (Or.inr (Or.inl ⟨-1,by simp,by norm_num⟩))

private lemma psi_finite_2_0_0_6 (P : PsiTheory) : P.psi 2 [0,0,6] = 1/1152 := by
  have h := P.string 2 [0,6] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_2_m1_6,psi_finite_2_0_5] at h
  exact h

private lemma psi_finite_3_0_6 (P : PsiTheory) : P.psi 3 [0,6] = 0 := by
  exact P.vanish 3 [0,6] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_0_6 (P : PsiTheory) : P.psi 0 [0,6] = 0 := by
  exact P.vanish 0 [0,6] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_2_0_6 (P : PsiTheory) : P.psi 2 [0,6] = 0 := by
  exact P.vanish 2 [0,6] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_0_6 (P : PsiTheory) : P.psi 1 [0,6] = 0 := by
  exact P.vanish 1 [0,6] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_3_2_6 (P : PsiTheory) : P.psi 3 [2,6] = 77/414720 := by
  have h := P.dvv 3 2 [6] (by norm_num) (by norm_num [complexity])
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,Finset.sum_insert,List.range_succ,selected,
    show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,
    show (Finset.range 2).powerset = {∅,{0},{1},{0,1}} from by decide,
    show (∅ : Finset ℕ) ≠ {0} from by decide,
    show (∅ : Finset ℕ) ≠ {1} from by decide,
    show (∅ : Finset ℕ) ≠ {0,1} from by decide,
    show ({0} : Finset ℕ) ≠ {1} from by decide,
    show ({0} : Finset ℕ) ≠ {0,1} from by decide,
    show ({1} : Finset ℕ) ≠ {0,1} from by decide,
    psi_finite_3_7,
    psi_finite_2_0_0_6,
    psi_finite_0_0,
    psi_finite_3_0_6,
    psi_finite_0_0_6,
    psi_finite_3_0,
    psi_finite_1_0,
    psi_finite_2_0_6,
    psi_finite_1_0_6,
    psi_finite_2_0] at h
  linarith

private lemma psi_finite_3_6_2 (P : PsiTheory) : P.psi 3 [6,2] = 77/414720 := by
  rw [P.symmetry 3 [6,2] [2,6] (by decide),psi_finite_3_2_6]

private lemma psi_finite_2_m1_2_5 (P : PsiTheory) : P.psi 2 [-1,2,5] = 0 := by
  exact P.vanish 2 [-1,2,5] (Or.inr (Or.inl ⟨-1,by simp,by norm_num⟩))

private lemma psi_finite_2_0_2_4 (P : PsiTheory) : P.psi 2 [0,2,4] = 11/1440 := by
  have h := P.string 2 [2,4] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_2_1_4,psi_finite_2_2_3] at h
  exact h

private lemma psi_finite_2_0_0_2_5 (P : PsiTheory) : P.psi 2 [0,0,2,5] = 1/90 := by
  have h := P.string 2 [0,2,5] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_2_m1_2_5,psi_finite_2_0_1_5,psi_finite_2_0_2_4] at h
  exact h

private lemma psi_finite_3_0_2_5 (P : PsiTheory) : P.psi 3 [0,2,5] = 0 := by
  exact P.vanish 3 [0,2,5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_0_2 (P : PsiTheory) : P.psi 0 [0,2] = 0 := by
  exact P.vanish 0 [0,2] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_3_0_2 (P : PsiTheory) : P.psi 3 [0,2] = 0 := by
  exact P.vanish 3 [0,2] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_0_2_5 (P : PsiTheory) : P.psi 0 [0,2,5] = 0 := by
  exact P.vanish 0 [0,2,5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_0_2_5 (P : PsiTheory) : P.psi 2 [0,2,5] = 0 := by
  exact P.vanish 2 [0,2,5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_0_2 (P : PsiTheory) : P.psi 2 [0,2] = 0 := by
  exact P.vanish 2 [0,2] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_0_2_5 (P : PsiTheory) : P.psi 1 [0,2,5] = 0 := by
  exact P.vanish 1 [0,2,5] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_3_2_2_5 (P : PsiTheory) : P.psi 3 [2,2,5] = 17/5760 := by
  have h := P.dvv 3 2 [2,5] (by norm_num) (by norm_num [complexity])
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,Finset.sum_insert,List.range_succ,selected,
    show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,
    show (Finset.range 2).powerset = {∅,{0},{1},{0,1}} from by decide,
    show (∅ : Finset ℕ) ≠ {0} from by decide,
    show (∅ : Finset ℕ) ≠ {1} from by decide,
    show (∅ : Finset ℕ) ≠ {0,1} from by decide,
    show ({0} : Finset ℕ) ≠ {1} from by decide,
    show ({0} : Finset ℕ) ≠ {0,1} from by decide,
    show ({1} : Finset ℕ) ≠ {0,1} from by decide,
    psi_finite_3_3_5,
    psi_finite_3_6_2,
    psi_finite_2_0_0_2_5,
    psi_finite_0_0,
    psi_finite_3_0_2_5,
    psi_finite_0_0_2,
    psi_finite_3_0_5,
    psi_finite_0_0_5,
    psi_finite_3_0_2,
    psi_finite_0_0_2_5,
    psi_finite_3_0,
    psi_finite_1_0,
    psi_finite_2_0_2_5,
    psi_finite_1_0_2,
    psi_finite_2_0_5,
    psi_finite_1_0_5,
    psi_finite_2_0_2,
    psi_finite_1_0_2_5,
    psi_finite_2_0] at h
  linarith

private lemma psi_finite_3_2_4 (P : PsiTheory) : P.psi 3 [2,4] = 0 := by
  exact P.vanish 3 [2,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_0_4 (P : PsiTheory) : P.psi 0 [0,4] = 0 := by
  exact P.vanish 0 [0,4] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_2_2_4 (P : PsiTheory) : P.psi 2 [2,4] = 0 := by
  exact P.vanish 2 [2,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_0_4 (P : PsiTheory) : P.psi 1 [0,4] = 0 := by
  exact P.vanish 1 [0,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_2_4 (P : PsiTheory) : P.psi 1 [2,4] = 0 := by
  exact P.vanish 1 [2,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_0_4 (P : PsiTheory) : P.psi 2 [0,4] = 0 := by
  exact P.vanish 2 [0,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_2_4 (P : PsiTheory) : P.psi 0 [2,4] = 0 := by
  exact P.vanish 0 [2,4] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_3_0_4 (P : PsiTheory) : P.psi 3 [0,4] = 0 := by
  exact P.vanish 3 [0,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_1_1_4 (P : PsiTheory) : P.psi 2 [1,1,4] = 1/96 := by
  have h := P.dilaton 2 [1,4] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_2_1_4] at h
  exact h

private lemma psi_finite_3_1_4 (P : PsiTheory) : P.psi 3 [1,4] = 0 := by
  exact P.vanish 3 [1,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_1_4 (P : PsiTheory) : P.psi 0 [1,4] = 0 := by
  exact P.vanish 0 [1,4] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_1_1_4 (P : PsiTheory) : P.psi 1 [1,4] = 0 := by
  exact P.vanish 1 [1,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_2_0_4 (P : PsiTheory) : P.psi 2 [2,0,4] = 11/1440 := by
  rw [P.symmetry 2 [2,0,4] [0,2,4] (by decide),psi_finite_2_0_2_4]

private lemma psi_finite_3_4_4 (P : PsiTheory) : P.psi 3 [4,4] = 607/1451520 := by
  have h := P.dvv 3 4 [4] (by norm_num) (by norm_num [complexity])
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,Finset.sum_insert,List.range_succ,selected,
    show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,
    show (Finset.range 2).powerset = {∅,{0},{1},{0,1}} from by decide,
    show (∅ : Finset ℕ) ≠ {0} from by decide,
    show (∅ : Finset ℕ) ≠ {1} from by decide,
    show (∅ : Finset ℕ) ≠ {0,1} from by decide,
    show ({0} : Finset ℕ) ≠ {1} from by decide,
    show ({0} : Finset ℕ) ≠ {0,1} from by decide,
    show ({1} : Finset ℕ) ≠ {0,1} from by decide,
    psi_finite_3_7,
    psi_finite_2_0_2_4,
    psi_finite_0_0,
    psi_finite_3_2_4,
    psi_finite_0_0_4,
    psi_finite_3_2,
    psi_finite_1_0,
    psi_finite_2_2_4,
    psi_finite_1_0_4,
    psi_finite_2_2,
    psi_finite_2_0,
    psi_finite_1_2_4,
    psi_finite_2_0_4,
    psi_finite_1_2,
    psi_finite_3_0,
    psi_finite_0_2_4,
    psi_finite_3_0_4,
    psi_finite_0_2,
    psi_finite_2_1_1_4,
    psi_finite_0_1,
    psi_finite_3_1_4,
    psi_finite_0_1_4,
    psi_finite_3_1,
    psi_finite_1_1,
    psi_finite_2_1_4,
    psi_finite_1_1_4,
    psi_finite_2_1,
    psi_finite_2_2_0_4] at h
  linarith

private lemma psi_finite_3_5_3 (P : PsiTheory) : P.psi 3 [5,3] = 503/1451520 := by
  rw [P.symmetry 3 [5,3] [3,5] (by decide),psi_finite_3_3_5]

private lemma psi_finite_2_m1_3_4 (P : PsiTheory) : P.psi 2 [-1,3,4] = 0 := by
  exact P.vanish 2 [-1,3,4] (Or.inr (Or.inl ⟨-1,by simp,by norm_num⟩))

private lemma psi_finite_2_0_3_3 (P : PsiTheory) : P.psi 2 [0,3,3] = 29/2880 := by
  have h := P.string 2 [3,3] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_2_2_3,psi_finite_2_3_2] at h
  exact h

private lemma psi_finite_2_0_0_3_4 (P : PsiTheory) : P.psi 2 [0,0,3,4] = 17/960 := by
  have h := P.string 2 [0,3,4] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_2_m1_3_4,psi_finite_2_0_2_4,psi_finite_2_0_3_3] at h
  exact h

private lemma psi_finite_3_0_3_4 (P : PsiTheory) : P.psi 3 [0,3,4] = 0 := by
  exact P.vanish 3 [0,3,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_3_0_3 (P : PsiTheory) : P.psi 3 [0,3] = 0 := by
  exact P.vanish 3 [0,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_0_3_4 (P : PsiTheory) : P.psi 0 [0,3,4] = 0 := by
  exact P.vanish 0 [0,3,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_0_3_4 (P : PsiTheory) : P.psi 2 [0,3,4] = 0 := by
  exact P.vanish 2 [0,3,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_0_3_4 (P : PsiTheory) : P.psi 1 [0,3,4] = 0 := by
  exact P.vanish 1 [0,3,4] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_3_2_3_4 (P : PsiTheory) : P.psi 3 [2,3,4] = 1121/241920 := by
  have h := P.dvv 3 2 [3,4] (by norm_num) (by norm_num [complexity])
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,Finset.sum_insert,List.range_succ,selected,
    show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,
    show (Finset.range 2).powerset = {∅,{0},{1},{0,1}} from by decide,
    show (∅ : Finset ℕ) ≠ {0} from by decide,
    show (∅ : Finset ℕ) ≠ {1} from by decide,
    show (∅ : Finset ℕ) ≠ {0,1} from by decide,
    show ({0} : Finset ℕ) ≠ {1} from by decide,
    show ({0} : Finset ℕ) ≠ {0,1} from by decide,
    show ({1} : Finset ℕ) ≠ {0,1} from by decide,
    psi_finite_3_4_4,
    psi_finite_3_5_3,
    psi_finite_2_0_0_3_4,
    psi_finite_0_0,
    psi_finite_3_0_3_4,
    psi_finite_0_0_3,
    psi_finite_3_0_4,
    psi_finite_0_0_4,
    psi_finite_3_0_3,
    psi_finite_0_0_3_4,
    psi_finite_3_0,
    psi_finite_1_0,
    psi_finite_2_0_3_4,
    psi_finite_1_0_3,
    psi_finite_2_0_4,
    psi_finite_1_0_4,
    psi_finite_2_0_3,
    psi_finite_1_0_3_4,
    psi_finite_2_0] at h
  linarith

private lemma psi_finite_2_1_2_3 (P : PsiTheory) : P.psi 2 [1,2,3] = 29/1440 := by
  have h := P.dilaton 2 [2,3] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_2_2_3] at h
  exact h

private lemma psi_finite_2_1_3_2 (P : PsiTheory) : P.psi 2 [1,3,2] = 29/1440 := by
  rw [P.symmetry 2 [1,3,2] [1,2,3] (by decide),psi_finite_2_1_2_3]

private lemma psi_finite_2_0_1_3_3 (P : PsiTheory) : P.psi 2 [0,1,3,3] = 29/576 := by
  have h := P.string 2 [1,3,3] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ,psi_finite_2_0_3_3,psi_finite_2_1_2_3,psi_finite_2_1_3_2] at h
  exact h

private lemma psi_finite_3_1_3_3 (P : PsiTheory) : P.psi 3 [1,3,3] = 0 := by
  exact P.vanish 3 [1,3,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_3_1_3 (P : PsiTheory) : P.psi 3 [1,3] = 0 := by
  exact P.vanish 3 [1,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_0_3_3 (P : PsiTheory) : P.psi 0 [0,3,3] = 0 := by
  exact P.vanish 0 [0,3,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_1_3_3 (P : PsiTheory) : P.psi 2 [1,3,3] = 0 := by
  exact P.vanish 2 [1,3,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_1_3 (P : PsiTheory) : P.psi 2 [1,3] = 0 := by
  exact P.vanish 2 [1,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_0_3_3 (P : PsiTheory) : P.psi 1 [0,3,3] = 0 := by
  exact P.vanish 1 [0,3,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_1_3_3 (P : PsiTheory) : P.psi 1 [1,3,3] = 0 := by
  exact P.vanish 1 [1,3,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_1_1_3 (P : PsiTheory) : P.psi 1 [1,3] = 0 := by
  exact P.vanish 1 [1,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_1_3_3 (P : PsiTheory) : P.psi 0 [1,3,3] = 0 := by
  exact P.vanish 0 [1,3,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_0_1_3 (P : PsiTheory) : P.psi 0 [1,3] = 0 := by
  exact P.vanish 0 [1,3] (Or.inl (by norm_num [Stable]))

private lemma psi_finite_3_0_3_3 (P : PsiTheory) : P.psi 3 [0,3,3] = 0 := by
  exact P.vanish 3 [0,3,3] (Or.inr (Or.inr (by norm_num)))

private lemma psi_finite_2_1_0_3_3 (P : PsiTheory) : P.psi 2 [1,0,3,3] = 29/576 := by
  rw [P.symmetry 2 [1,0,3,3] [0,1,3,3] (by decide),psi_finite_2_0_1_3_3]

private lemma psi_finite_3_3_3_3 (P : PsiTheory) : P.psi 3 [3,3,3] = 583/96768 := by
  have h := P.dvv 3 3 [3,3] (by norm_num) (by norm_num [complexity])
  norm_num [dvvRHS,weighted,doubleWeight,oddFactorial,Finset.prod_range_succ,
    Finset.sum_range_succ,Finset.sum_insert,List.range_succ,selected,
    show ({0} : Finset ℕ).powerset = {∅,{0}} from by decide,
    show (Finset.range 2).powerset = {∅,{0},{1},{0,1}} from by decide,
    show (∅ : Finset ℕ) ≠ {0} from by decide,
    show (∅ : Finset ℕ) ≠ {1} from by decide,
    show (∅ : Finset ℕ) ≠ {0,1} from by decide,
    show ({0} : Finset ℕ) ≠ {1} from by decide,
    show ({0} : Finset ℕ) ≠ {0,1} from by decide,
    show ({1} : Finset ℕ) ≠ {0,1} from by decide,
    psi_finite_3_5_3,
    psi_finite_2_0_1_3_3,
    psi_finite_0_0,
    psi_finite_3_1_3_3,
    psi_finite_0_0_3,
    psi_finite_3_1_3,
    psi_finite_0_0_3_3,
    psi_finite_3_1,
    psi_finite_1_0,
    psi_finite_2_1_3_3,
    psi_finite_1_0_3,
    psi_finite_2_1_3,
    psi_finite_1_0_3_3,
    psi_finite_2_1,
    psi_finite_2_0,
    psi_finite_1_1_3_3,
    psi_finite_2_0_3,
    psi_finite_1_1_3,
    psi_finite_2_0_3_3,
    psi_finite_1_1,
    psi_finite_3_0,
    psi_finite_0_1_3_3,
    psi_finite_3_0_3,
    psi_finite_0_1_3,
    psi_finite_3_0_3_3,
    psi_finite_0_1,
    psi_finite_2_1_0_3_3] at h
  linarith

lemma pureC_genus_three_two_two_five (P : PsiTheory) : pureC P 3 [2,2,5] = 6545/23328 := by
  norm_num [pureC,pure,complexity,oddFactorial,Finset.prod_range_succ,psi_finite_3_2_2_5]

lemma pureC_genus_three_two_three_four (P : PsiTheory) : pureC P 3 [2,3,4] = 39235/139968 := by
  norm_num [pureC,pure,complexity,oddFactorial,Finset.prod_range_succ,psi_finite_3_2_3_4]

lemma pureC_genus_three_three_three_three (P : PsiTheory) : pureC P 3 [3,3,3] = 714175/2519424 := by
  norm_num [pureC,pure,complexity,oddFactorial,Finset.prod_range_succ,psi_finite_3_3_3_3]

end WP
