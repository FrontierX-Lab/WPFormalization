import Mathlib

/-! Uniqueness of genuine inverse-power asymptotic coefficients along any
scale tending to infinity. This will identify coefficient constructions from
proved remainders; it does not assume or establish those remainders. -/
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology

def HasInversePowerExpansion (f scale : ℕ → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G,
    0 < scale g ∧ |f g-∑ j ∈ Finset.range (K+1), a j/(scale g)^j| ≤ C/(scale g)^(K+1)

lemma inverse_power_expansion_unique (f scale : ℕ → ℝ) (a b : ℕ → ℝ)
    (hscale : Tendsto scale atTop atTop)
    (ha : HasInversePowerExpansion f scale a) (hb : HasInversePowerExpansion f scale b) :
    a = b := by
  funext K
  induction K using Nat.strong_induction_on with
  | h K ih =>
    obtain ⟨Ca,hCa,Ga,ha⟩ := ha K
    obtain ⟨Cb,hCb,Gb,hb⟩ := hb K
    by_contra hne
    have hδ : 0 < |a K-b K| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨Gs,hGs⟩ := eventually_atTop.mp (hscale.eventually
      (eventually_gt_atTop ((Ca+Cb)/|a K-b K|)))
    let g := max Ga (max Gb Gs)
    have hga : Ga ≤ g := le_max_left _ _
    have hgb : Gb ≤ g := (le_max_left _ _).trans (le_max_right _ _)
    have hgs : Gs ≤ g := (le_max_right _ _).trans (le_max_right _ _)
    have hA := ha g hga
    have hB := hb g hgb
    have hh : 0 < scale g := hA.1
    have hp : ∑ j ∈ Finset.range K, a j/(scale g)^j = ∑ j ∈ Finset.range K, b j/(scale g)^j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (Finset.mem_range.mp hj)]
    have he : (a K-b K)/(scale g)^K =
        (f g-∑ j ∈ Finset.range (K+1), b j/(scale g)^j)-
        (f g-∑ j ∈ Finset.range (K+1), a j/(scale g)^j) := by
      rw [Finset.sum_range_succ,Finset.sum_range_succ,hp]
      ring
    have hbound : |a K-b K|/(scale g)^K ≤ (Ca+Cb)/(scale g)^(K+1) := by
      rw [←abs_of_pos (pow_pos hh K),←abs_div,he]
      exact (abs_sub _ _).trans (by
        calc _ ≤ Cb/(scale g)^(K+1)+Ca/(scale g)^(K+1) := add_le_add hB.2 hA.2
             _ = (Ca+Cb)/(scale g)^(K+1) := by ring)
    have hsmall : |a K-b K| ≤ (Ca+Cb)/scale g := by
      have hc := (div_le_iff₀ (pow_pos hh K)).mp hbound
      have hid : (Ca+Cb)/(scale g)^(K+1)*(scale g)^K = (Ca+Cb)/scale g := by
        rw [pow_succ]
        field_simp [hh.ne']
      rwa [hid] at hc
    have hbig : (Ca+Cb)/scale g < |a K-b K| := by
      apply (div_lt_iff₀ hh).mpr
      have hc := (div_lt_iff₀ hδ).mp (hGs g hgs)
      nlinarith
    exact (not_lt_of_ge hsmall) hbig
end WP.HigherOrder
