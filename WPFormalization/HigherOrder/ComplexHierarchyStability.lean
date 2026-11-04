import WPFormalization.HigherOrder.ComplexTriangular
/-! Prefix stability for the actual complex triangular algorithm. -/
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

lemma nextJet_coeff_below (P : PsiTheory) (R : ℂ → ℂ) (z : ℂ) (K : ℕ) (F : HierarchyJet)
    (k : ℕ) (hk : k<K) :
    (∀ d,PowerSeries.coeff k ((nextJet P R z K F).profile d)=PowerSeries.coeff k (F.profile d)) ∧
    (∀ p,PowerSeries.coeff k ((nextJet P R z K F).cusp p)=PowerSeries.coeff k (F.cusp p)) ∧
    (∀ p,PowerSeries.coeff k ((nextJet P R z K F).genus p)=PowerSeries.coeff k (F.genus p)) := by
  have hn : k≠K := by omega
  constructor
  · intro d
    simp only [nextJet,setCoeff,PowerSeries.coeff_mk,ite_eq_right hn]
  constructor
  · intro p
    simp only [nextJet,setCoeff,PowerSeries.coeff_mk,ite_eq_right hn]
  · intro p
    by_cases hp0 : p=0
    · subst p
      simp only [nextJet,ite_true,setCoeff,PowerSeries.coeff_mk,ite_eq_right hn]
    · by_cases hp1 : p=1
      · subst p
        simp only [nextJet,ite_true,ite_eq_right one_ne_zero,setCoeff,PowerSeries.coeff_mk,ite_eq_right hn]
      · simp only [nextJet,ite_eq_right hp0,ite_eq_right hp1,setCoeff,PowerSeries.coeff_mk,ite_eq_right hn]

lemma nextJet_unit_constants (P : PsiTheory) (R : ℂ → ℂ) (z : ℂ) (K : ℕ) (hK : 0<K)
    (F : HierarchyJet)
    (hF : (∀d,PowerSeries.constantCoeff (F.profile d)=1) ∧
      (∀p,PowerSeries.constantCoeff (F.cusp p)=1) ∧ (∀p,PowerSeries.constantCoeff (F.genus p)=1)) :
    (∀d,PowerSeries.constantCoeff ((nextJet P R z K F).profile d)=1) ∧
    (∀p,PowerSeries.constantCoeff ((nextJet P R z K F).cusp p)=1) ∧
    (∀p,PowerSeries.constantCoeff ((nextJet P R z K F).genus p)=1) := by
  have hp := nextJet_coeff_below P R z K F 0 hK
  simp only [PowerSeries.coeff_zero_eq_constantCoeff] at hp
  exact ⟨fun d=>(hp.1 d).trans (hF.1 d),fun p=>(hp.2.1 p).trans (hF.2.1 p),fun p=>(hp.2.2 p).trans (hF.2.2 p)⟩

lemma hierarchy_cusp_stable (P : PsiTheory) (R : ℂ → ℂ) (z : ℂ) (p n k : ℕ) (hk : k≤n) :
    PowerSeries.coeff k ((hierarchyJet P R z n).cusp p)=cuspCoefficient P R z p k := by
  induction n with
  | zero =>
    have hk0 : k=0 := by omega
    subst k
    rfl
  | succ n ih =>
    by_cases h : k=n+1
    · subst k
      rfl
    · rw [hierarchyJet,(nextJet_coeff_below P R z (n+1) (hierarchyJet P R z n) k (by omega)).2.1 p]
      exact ih (by omega)

lemma hierarchy_genus_stable (P : PsiTheory) (R : ℂ → ℂ) (z : ℂ) (p n k : ℕ) (hk : k≤n) :
    PowerSeries.coeff k ((hierarchyJet P R z n).genus p)=genusCoefficient P R z p k := by
  induction n with
  | zero =>
    have hk0 : k=0 := by omega
    subst k
    rfl
  | succ n ih =>
    by_cases h : k=n+1
    · subst k
      rfl
    · rw [hierarchyJet,(nextJet_coeff_below P R z (n+1) (hierarchyJet P R z n) k (by omega)).2.2 p]
      exact ih (by omega)

end WP.HigherOrder.ComplexCanonical
