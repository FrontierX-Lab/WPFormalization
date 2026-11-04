import WPFormalization.HigherOrder.MajorantLocality

/-! Actual formal solution of the strictly triangular system.
The coefficient with degree j and row i is constructed at natural-number code
i+m*j. All values used by its finite substitution have smaller code. This is
a well-founded recursion, not an assumed formal solution or fixed-point field.
-/
noncomputable section
namespace WP.Majorant
variable {R : Type*} [CommSemiring R]

lemma code_earlier {m : ℕ} (j k : ℕ) (i l : Fin m) (h : earlier j i k l) :
    l.val+m*k < i.val+m*j := by
  rcases h with hk | ⟨rfl,hl⟩
  · have hm := Nat.mul_le_mul_left m (show k+1 ≤ j by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hm
    have hl := l.isLt
    omega
  · omega

lemma code_div {m : ℕ} (hm : 0 < m) (j : ℕ) (i : Fin m) :
    (i.val+m*j)/m = j := by
  rw [Nat.add_mul_div_left _ _ hm,Nat.div_eq_of_lt i.isLt]
  simp

lemma code_mod {m : ℕ} (j : ℕ) (i : Fin m) : (i.val+m*j)%m = i.val := by
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt i.isLt]

def coefficientStep {m : ℕ} (hm : 0 < m)
    (Φ : Fin m → MvPowerSeries (Option (Fin m)) R)
    (n : ℕ) (lower : ∀ k < n, R) : R :=
  if n/m = 0 then 0 else
    substitutionCoeff (Φ ⟨n%m,Nat.mod_lt n hm⟩)
      (fun l => PowerSeries.mk (fun k => if h : l.val+m*k < n then lower (l.val+m*k) h else 0)) (n/m)

def coefficientTable {m : ℕ} (hm : 0 < m)
    (Φ : Fin m → MvPowerSeries (Option (Fin m)) R) (n : ℕ) : R :=
  Nat.strongRec (coefficientStep hm Φ) n

lemma coefficientTable_eq {m : ℕ} (hm : 0 < m)
    (Φ : Fin m → MvPowerSeries (Option (Fin m)) R) (n : ℕ) :
    coefficientTable hm Φ n = if n/m = 0 then 0 else
      substitutionCoeff (Φ ⟨n%m,Nat.mod_lt n hm⟩)
        (fun l => PowerSeries.mk (fun k => if l.val+m*k < n then coefficientTable hm Φ (l.val+m*k) else 0)) (n/m) := by
  rw [coefficientTable,Nat.strongRec_eq]
  rfl

lemma coefficientTable_zero {m : ℕ} (hm : 0 < m)
    (Φ : Fin m → MvPowerSeries (Option (Fin m)) R) (i : Fin m) : coefficientTable hm Φ i.val = 0 := by
  rw [coefficientTable_eq]
  simp [Nat.div_eq_of_lt i.isLt]

def formalSolution {m : ℕ} (hm : 0 < m)
    (Φ : Fin m → MvPowerSeries (Option (Fin m)) R) (i : Fin m) : PowerSeries R :=
  PowerSeries.mk (fun j => coefficientTable hm Φ (i.val+m*j))

lemma formalSolution_zero {m : ℕ} (hm : 0 < m)
    (Φ : Fin m → MvPowerSeries (Option (Fin m)) R) :
    ∀ i, PowerSeries.coeff 0 (formalSolution hm Φ i) = 0 := by
  intro i
  simp [formalSolution,coefficientTable_zero]

lemma formalSolution_fixedPoint {m : ℕ} (hm : 0 < m)
    (Φ : Fin m → MvPowerSeries (Option (Fin m)) R)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (Φ i) = 0)
    (htri : ∀ i l : Fin m, i.val ≤ l.val → MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i) = 0) :
    ∀ i j, PowerSeries.coeff j (formalSolution hm Φ i) = substitutionCoeff (Φ i) (formalSolution hm Φ) j := by
  intro i j
  by_cases hj : j = 0
  · subst j
    rw [formalSolution_zero,substitutionCoeff_zero,hzero]
  · rw [formalSolution,PowerSeries.coeff_mk,coefficientTable_eq,code_div hm j i,if_neg hj]
    have hi : (⟨(i.val+m*j)%m,Nat.mod_lt _ hm⟩ : Fin m) = i := by
      apply Fin.ext
      exact code_mod j i
    rw [hi]
    let E : Fin m → PowerSeries R := fun l => PowerSeries.mk (fun k =>
      if l.val+m*k < i.val+m*j then coefficientTable hm Φ (l.val+m*k) else 0)
    have hE₀ : ∀ l, PowerSeries.coeff 0 (E l) = 0 := by
      intro l
      simp [E,coefficientTable_zero]
    change substitutionCoeff (Φ i) E j = substitutionCoeff (Φ i) (formalSolution hm Φ) j
    apply substitutionCoeff_congr_earlier j (by omega) i (Φ i) E (formalSolution hm Φ)
      hE₀ (formalSolution_zero hm Φ) (htri i)
    intro l k he
    simp [E,formalSolution,code_earlier j k i l he]

lemma formal_exists {m : ℕ} (Φ : Fin m → MvPowerSeries (Option (Fin m)) R)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (Φ i) = 0)
    (htri : ∀ i l : Fin m, i.val ≤ l.val → MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i) = 0) :
    ∃ U : Fin m → PowerSeries R, (∀ i, PowerSeries.coeff 0 (U i) = 0) ∧
      ∀ i j, PowerSeries.coeff j (U i) = substitutionCoeff (Φ i) U j := by
  by_cases hm : m = 0
  · subst m
    refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i j; exact Fin.elim0 i
  · have hm₀ : 0 < m := by omega
    exact ⟨formalSolution hm₀ Φ,formalSolution_zero hm₀ Φ,formalSolution_fixedPoint hm₀ Φ hzero htri⟩

end WP.Majorant
