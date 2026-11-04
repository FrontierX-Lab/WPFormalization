import Mathlib
/-! Finite reflection of genera, node degrees, and complementary external label sets. -/

noncomputable section
namespace WP.Analysis
lemma sum_powerset_complement (R : Finset ℕ) (f : Finset ℕ→ℝ) :
    (∑ I ∈ R.powerset,f I)=(∑ I ∈ R.powerset,f (R\I)) := by
  classical
  apply Finset.sum_bij (fun I _ => R\I)
  · intro I hI
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro I hI J hJ hIJ
    have hi := Finset.mem_powerset.mp hI
    have hj := Finset.mem_powerset.mp hJ
    have he := congrArg (fun K => R\K) hIJ
    simpa only [Finset.sdiff_sdiff_eq_self hi,Finset.sdiff_sdiff_eq_self hj] using he
  · intro I hI
    refine ⟨R\I,Finset.mem_powerset.mpr Finset.sdiff_subset,?_⟩
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hI)
  · intro I hI
    rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hI)]

lemma finite_splitting_sum_reflect (k g : ℕ) (R : Finset ℕ)
    (f : ℕ→ℕ→Finset ℕ→ℝ) :
    (∑ u ∈ Finset.range (k-1), ∑ j ∈ Finset.range (g+1), ∑ I ∈ R.powerset,f u j I)=
      ∑ u ∈ Finset.range (k-1), ∑ j ∈ Finset.range (g+1), ∑ I ∈ R.powerset,
        f (k-2-u) (g-j) (R\I) := by
  rw [←Finset.sum_range_reflect (fun u => ∑ j ∈ Finset.range (g+1), ∑ I ∈ R.powerset,f u j I) (k-1)]
  apply Finset.sum_congr rfl
  intro u hu
  have hkk : k-1-1=k-2 := by omega
  rw [hkk,←Finset.sum_range_reflect (fun j => ∑ I ∈ R.powerset,f (k-2-u) j I) (g+1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.add_sub_cancel]
  exact sum_powerset_complement R (fun I => f (k-2-u) (g-j) I)
end WP.Analysis
