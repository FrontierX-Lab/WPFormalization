import WPFormalization.Intersection.ShiftedStringDerivative
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
noncomputable section
namespace WP
/-- A finite coordinate box used only for exact finite reindexing. -/
def externalDegreeBox (p B : ℕ) : Finset (Fin p → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range (B+1))
@[simp] lemma mem_externalDegreeBox (p B : ℕ) (b : Fin p → ℕ) :
    b ∈ externalDegreeBox p B ↔ ∀ i, b i ≤ B := by
  simp [externalDegreeBox, Nat.lt_succ_iff]

lemma externalDegreeBox_lowering {p B : ℕ} (i : Fin p)
    (F : (Fin p → ℕ) → (Fin p → ℕ) → ℝ) :
    (∑ b ∈ externalDegreeBox p B, if 0 < b i then F b (Function.update b i (b i-1)) else 0) =
    ∑ b ∈ externalDegreeBox p B, if b i < B then F (Function.update b i (b i+1)) b else 0 := by
  rw [←Finset.sum_filter,←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun b _ => Function.update b i (b i+1))
  · intro b hb
    obtain ⟨hb,hpos⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨mem_externalDegreeBox p B _ |>.mpr ?_,by simp⟩
    intro j
    by_cases hj : j=i
    · subst j
      simpa using Nat.succ_le_of_lt hpos
    · simp only [Function.update_of_ne hj]
      exact (mem_externalDegreeBox p B b |>.mp hb) j
  · intro b hb c hc he
    have hrev : ∀ d : Fin p → ℕ,
        Function.update (Function.update d i (d i+1)) i
          ((Function.update d i (d i+1)) i-1) = d := by intro d;simp
    have := congrArg (fun d : Fin p → ℕ => Function.update d i (d i-1)) he
    simpa only [hrev] using this
  · intro b hb
    obtain ⟨hb,hpos⟩ := Finset.mem_filter.mp hb
    refine ⟨Function.update b i (b i-1), Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
    · apply (mem_externalDegreeBox p B _).mpr
      intro j
      by_cases hj : j=i
      · subst j
        simpa using (Nat.sub_le (b i) 1).trans ((mem_externalDegreeBox p B b).mp hb i)
      · simp only [Function.update_of_ne hj]
        exact (mem_externalDegreeBox p B b).mp hb j
    · simp only [Function.update_self]
      have hle := (mem_externalDegreeBox p B b).mp hb i
      omega
    · simp [Nat.sub_add_cancel (by omega : 1 ≤ b i)]
  · intro b hb
    simp
end WP
namespace WP
lemma hasDerivAt_external_product {p : ℕ} (K : Fin p → ℕ → ℝ → ℝ)
    (b : Fin p → ℕ) (Y : ℝ) (hK : ∀ i n, HasDerivAt (K i n) (K i (n+1) Y) Y) :
    HasDerivAt (fun y => ∏ i, K i (b i) y)
      (∑ i, ∏ j, K j (Function.update b i (b i+1) j) Y) Y := by
  have hd := HasDerivAt.fun_finsetProd (u:=Finset.univ) (fun i _ => hK i (b i))
  convert! hd using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self, smul_eq_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

/-- Exact finite cancellation for the degree-lowering part of the string law. -/
lemma externalDegreeBox_cancel {p B : ℕ} (U : (Fin p → ℕ) → ℝ)
    (K : Fin p → ℕ → ℝ) (hzero : ∀ b ∈ externalDegreeBox p B, ∀ i, b i = B → U b = 0) :
    (∑ b ∈ externalDegreeBox p B,
      (∏ i, K i (b i)) * (∑ i, if 0 < b i then U (Function.update b i (b i-1)) else 0)) =
    ∑ b ∈ externalDegreeBox p B, (∑ i, ∏ j, K j (Function.update b i (b i+1) j)) * U b := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have he := externalDegreeBox_lowering (B:=B) i
    (fun b c => (∏ j, K j (b j)) * U c)
  simp_rw [mul_ite, mul_zero] at *
  rw [he]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hlt : b i < B
  · simp [hlt]
  · have hbi : b i = B := by have := (mem_externalDegreeBox p B b).mp hb i;omega
    simp [hlt,hzero b hb i hbi]

lemma hasDerivAt_externalDegreeBox {p B : ℕ}
    (U : ℕ → (Fin p → ℕ) → ℝ → ℝ) (K : Fin p → ℕ → ℝ → ℝ)
    (q : ℕ) (Y A : ℝ)
    (hU : ∀ b ∈ externalDegreeBox p B, HasDerivAt (U q b)
      (A*U (q+1) b Y - ∑ i, if 0 < b i then U q (Function.update b i (b i-1)) Y else 0) Y)
    (hK : ∀ i n, HasDerivAt (K i n) (K i (n+1) Y) Y)
    (hzero : ∀ b ∈ externalDegreeBox p B, ∀ i, b i = B → U q b Y = 0) :
    HasDerivAt (fun y => ∑ b ∈ externalDegreeBox p B, U q b y * ∏ i, K i (b i) y)
      (A * ∑ b ∈ externalDegreeBox p B, U (q+1) b Y * ∏ i, K i (b i) Y) Y := by
  have hd := HasDerivAt.fun_sum (u:=externalDegreeBox p B) (fun b hb =>
    (hU b hb).mul (hasDerivAt_external_product K b Y hK))
  convert! hd using 1
  simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have he := externalDegreeBox_cancel (fun b => U q b Y) (fun i n => K i n Y) hzero
  have he' : (∑ b ∈ externalDegreeBox p B,
      (∑ i, if 0 < b i then U q (Function.update b i (b i-1)) Y else 0) * ∏ i, K i (b i) Y) =
      ∑ b ∈ externalDegreeBox p B, U q b Y * (∑ i, ∏ j, K j (Function.update b i (b i+1) j) Y) := by
    simpa only [mul_comm] using he
  rw [he']
  have hm : (∑ b ∈ externalDegreeBox p B, A * U (q+1) b Y * ∏ i, K i (b i) Y) =
      ∑ b ∈ externalDegreeBox p B, A * (U (q+1) b Y * ∏ i, K i (b i) Y) := by
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hm]
  simp only [←Finset.mul_sum]
  ring
end WP
