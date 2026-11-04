import Mathlib

/-! Finite enumeration of stable splitting components with complexity loss two. -/

noncomputable section
open Set

noncomputable section
namespace WP.Analysis
lemma finite_loss_two_sum (g : ℕ) (hg : 1 ≤ g) (R : Finset ℕ)
    (f : ℕ→Finset ℕ→ℝ) :
    (∑ j ∈ Finset.range (g+1),∑ I ∈ R.powerset,if 2*j+I.card=2 then f j I else 0)=
      (∑ I ∈ R.powerset,if I.card=2 then f 0 I else 0)+
      (∑ I ∈ R.powerset,if I.card=0 then f 1 I else 0) := by
  have hp (j : ℕ) :
      (∑ I ∈ R.powerset,if 2*j+I.card=2 then f j I else 0)=
      (if j=0 then (∑ I ∈ R.powerset,if I.card=2 then f 0 I else 0) else 0)+
      (if j=1 then (∑ I ∈ R.powerset,if I.card=0 then f 1 I else 0) else 0) := by
    by_cases h0 : j=0
    · subst j
      simp
    · by_cases h1 : j=1
      · subst j
        simp
      · simp only [if_neg h0,if_neg h1,zero_add]
        apply Finset.sum_eq_zero
        intro I hI
        exact if_neg (by omega)
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  simp [show 1<g+1 by omega]

lemma sum_card_zero (R : Finset ℕ) (f : Finset ℕ→ℝ) :
    (∑ I ∈ R.powerset,if I.card=0 then f I else 0)=f ∅ := by
  classical
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro I hI hne
    exact if_neg (by simpa only [Finset.card_eq_zero] using hne)
  · simp
end WP.Analysis
