import WPFormalization.HigherOrder.ProfileSplitting
/-! The true one-orientation low-loss profile sum agrees exactly with the
finite actual counterpart of C.16. Small-weight geometry supplies all valid
large components and the finite genus cutoff. Every shift, signed node degree,
stability guard and labeled child profile is retained. -/
noncomputable section
namespace WP.HigherOrder
open Set

lemma small_weight_parent_genus_large (g p L:ℕ)(S:ℝ)(hp:1 ≤ p)(hL:1 ≤ L)
    (hs:Stable g p)(hS:(p:ℝ)+2*L ≤ S)(hsmall:S^2/(complexity g p:ℝ)<1) : L+1<g := by
  have hh:0<(complexity g p:ℝ) := by
    have hn:0<complexity g p := by unfold complexity Stable at *;omega
    exact_mod_cast hn
  have heq:(complexity g p:ℝ)=2*(g:ℝ)+p-2 := by
    unfold complexity
    rw [Nat.cast_sub (by unfold Stable at *;omega)]
    push_cast
    ring
  have hpR:(1:ℝ) ≤ p := by exact_mod_cast hp
  have hLR:(1:ℝ) ≤ L := by exact_mod_cast hL
  have hS1:1 ≤ S := by linarith
  have hSS:S ≤ S^2 := by nlinarith
  have hbig:S^2<(complexity g p:ℝ) := (div_lt_one hh).mp hsmall
  have hgR:(L:ℝ)+1<(g:ℝ) := by rw [heq] at hbig;linarith
  exact_mod_cast hgR

/-- The exact finite actual counterpart of the retained rule C.16 at order L-1. -/
def recursiveSeparatingLowCore (P:PsiTheory)(g k L:ℕ)(d:List ℕ)(Y:ℝ):ℝ :=
  ∑j∈Finset.range L,∑I∈(Finset.range d.length).powerset,
    if Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ L-1 then
      (A Y/(complexity g (d.length+1):ℝ))^(2*j+I.card)*
        actualLargeRatioCore P g (d.length+1) j I.card Y*
          ∑u∈Finset.range (k-1),smallW P Y j (u::selectedNat d I)*
            profile P (g-j) ((k-2-u)::selectedNat d ((Finset.range d.length)\I)) Y
    else 0

lemma recursiveSeparatingLow_exact_core (P:PsiTheory)(g k L:ℕ)(d:List ℕ)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(S:ℝ)(hL:1 ≤ L)(hs:Stable g (d.length+1))
    (hS:((d.length+1:ℕ):ℝ)+2*L ≤ S)(hsmall:S^2/(complexity g (d.length+1):ℝ)<1) :
    recursiveSeparatingLow P g k L d Y=recursiveSeparatingLowCore P g k L d Y := by
  have hgL:=small_weight_parent_genus_large g (d.length+1) L S (by omega) hL hs hS hsmall
  have hcore:recursiveSeparatingLow P g k L d Y=
      ∑j∈Finset.range (g+1),∑I∈(Finset.range d.length).powerset,
        if Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ L-1 then
          (A Y/(complexity g (d.length+1):ℝ))^(2*j+I.card)*
            actualLargeRatioCore P g (d.length+1) j I.card Y*
              ∑u∈Finset.range (k-1),smallW P Y j (u::selectedNat d I)*
                profile P (g-j) ((k-2-u)::selectedNat d ((Finset.range d.length)\I)) Y
        else 0 := by
    unfold recursiveSeparatingLow
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hI
    have hIs:=Finset.mem_powerset.mp hI
    have hcard:I.card ≤ d.length := by simpa only [Finset.card_range] using Finset.card_le_card hIs
    have hguard:(2 ≤ 2*j+I.card ∧ 2*j+I.card<L) ↔
        Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ L-1 := by unfold Stable;omega
    by_cases hr:2 ≤ 2*j+I.card ∧ 2*j+I.card<L
    · simp only [if_pos hr,if_pos (hguard.mp hr)]
      have hv:=small_weight_split_child_valid g (d.length+1) j I.card L S
        (by omega) hL hs hS hsmall (by omega) (by omega)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [recursiveSeparatingTerm_exact_core P g k j u d I hu hv.1 hIs hv.2 Y hY]
      ring
    · simp only [if_neg hr,if_neg (fun h=>hr (hguard.mpr h)),Finset.sum_const_zero]
  rw [hcore]
  unfold recursiveSeparatingLowCore
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : L ≤ g+1))
  intro j hj hjnot
  have hjL:L ≤ j := by simpa only [Finset.mem_range,not_lt] using hjnot
  apply Finset.sum_eq_zero
  intro I hI
  have hn:¬(Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ L-1) := by omega
  rw [if_neg hn]

end WP.HigherOrder
