import WPFormalization.HigherOrder.AsymptoticUniqueness
/-! Uniqueness of actual vector-valued inverse-power asymptotics.
Applied to complex PI jumps, this identifies the Borel coefficients with the
canonical fixed-order coefficients from two independently proved remainders.
The expansion predicates are helper hypotheses, not external mathematics. -/
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology

def HasVectorInversePowerExpansion {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ→E) (scale:ℕ→ℝ) (a:ℕ→E) : Prop :=
  ∀K:ℕ,∃C:ℝ,0<C ∧ ∃G:ℕ,∀g≥G,0<scale g ∧
    ‖f g-∑j∈Finset.range (K+1),((scale g)^j)⁻¹ • a j‖≤C/(scale g)^(K+1)
lemma vector_inverse_power_expansion_unique {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f:ℕ→E) (scale:ℕ→ℝ) (a b:ℕ→E)
    (hscale:Tendsto scale atTop atTop)
    (ha:HasVectorInversePowerExpansion f scale a)
    (hb:HasVectorInversePowerExpansion f scale b) : a=b := by
  funext K
  induction K using Nat.strong_induction_on with
  | h K ih =>
    obtain ⟨Ca,hCa,Ga,ha⟩:=ha K
    obtain ⟨Cb,hCb,Gb,hb⟩:=hb K
    by_contra hne
    have hδ : 0<‖a K-b K‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨Gs,hGs⟩:=eventually_atTop.mp (hscale.eventually
      (eventually_gt_atTop ((Ca+Cb)/‖a K-b K‖)))
    let g:=max Ga (max Gb Gs)
    have hga : Ga≤g:=le_max_left _ _
    have hgb : Gb≤g:=(le_max_left _ _).trans (le_max_right _ _)
    have hgs : Gs≤g:=(le_max_right _ _).trans (le_max_right _ _)
    have hA:=ha g hga
    have hB:=hb g hgb
    have hh : 0<scale g:=hA.1
    have hp : ∑j∈Finset.range K,((scale g)^j)⁻¹ • a j=
        ∑j∈Finset.range K,((scale g)^j)⁻¹ • b j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (Finset.mem_range.mp hj)]
    have he : ((scale g)^K)⁻¹ • (a K-b K)=
        (f g-∑j∈Finset.range (K+1),((scale g)^j)⁻¹ • b j)-
        (f g-∑j∈Finset.range (K+1),((scale g)^j)⁻¹ • a j) := by
      rw [Finset.sum_range_succ,Finset.sum_range_succ,hp,smul_sub]
      abel
    have hbound : ‖a K-b K‖/(scale g)^K≤(Ca+Cb)/(scale g)^(K+1) := by
      calc
        _ = ‖((scale g)^K)⁻¹ • (a K-b K)‖ := by
          rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_pow,abs_of_pos hh]
          ring
        _ ≤ ‖f g-∑j∈Finset.range (K+1),((scale g)^j)⁻¹ • b j‖+
            ‖f g-∑j∈Finset.range (K+1),((scale g)^j)⁻¹ • a j‖ := by
          rw [he]
          exact norm_sub_le _ _
        _ ≤ Cb/(scale g)^(K+1)+Ca/(scale g)^(K+1) := add_le_add hB.2 hA.2
        _ = (Ca+Cb)/(scale g)^(K+1) := by ring
    have hsmall : ‖a K-b K‖≤(Ca+Cb)/scale g := by
      have hc:=(div_le_iff₀ (pow_pos hh K)).mp hbound
      have hid : (Ca+Cb)/(scale g)^(K+1)*(scale g)^K=(Ca+Cb)/scale g := by
        rw [pow_succ]
        field_simp [hh.ne']
      rwa [hid] at hc
    have hbig : (Ca+Cb)/scale g<‖a K-b K‖ := by
      apply (div_lt_iff₀ hh).mpr
      have hc:=(div_lt_iff₀ hδ).mp (hGs g hgs)
      nlinarith
    exact (not_lt_of_ge hsmall) hbig
end WP.HigherOrder
