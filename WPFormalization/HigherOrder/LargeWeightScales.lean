import WPFormalization.HigherOrder.LargeWeightRemainder
/-! The large-weight remainder bound remains uniform when the single
order-scale parameter M is increased. C/B/M₀ are chosen before every
M≥M₀ and before every actual state, tuple, order and parameter. This lets
the C.3 remainder induction choose a common larger scale. -/
noncomputable section
namespace WP.HigherOrder
lemma canonical_large_weight_remainders_all_scales (P:PsiTheory) (δ₀:ℝ) (hδ₀:0<δ₀) :
    ∃ C B:ℝ, ∃ M₀:ℕ,0<C ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
      (∀g:ℕ,∀d:List ℕ,1 ≤ d.length→Stable g d.length→1 ≤ complexity g d.length→
      ∀L:ℕ,1 ≤ L→∀Y∈Set.Icc (0:ℝ) y₀,
      δ₀ ≤ profileOrderWeight (M:ℝ) L d^2/(complexity g d.length:ℝ)→
      |profile P g d Y-∑j∈Finset.range L,profileCoefficient P Y d j/(complexity g d.length:ℝ)^j| ≤
        C*B^L*profileOrderWeight (M:ℝ) L d^(2*L)/(complexity g d.length:ℝ)^L) ∧
      (∀g p:ℕ,1 ≤ p→Stable g p→1 ≤ complexity g p→
      ∀L:ℕ,1 ≤ L→∀Y∈Set.Icc (0:ℝ) y₀,
      δ₀ ≤ scalarOrderWeight (M:ℝ) L p^2/(complexity g p:ℝ)→
      |cuspCorrection P g p Y-∑j∈Finset.range L,cuspCoefficient P Y p j/(complexity g p:ℝ)^j|+
      |genusCorrection P g p Y-∑j∈Finset.range L,genusCoefficient P Y p j/(complexity g p:ℝ)^j| ≤
        C*B^L*scalarOrderWeight (M:ℝ) L p^(2*L)/(complexity g p:ℝ)^L) := by
  obtain ⟨C,B,M₀,hC,hB,hM₀,hcoef₀,hscalar₀⟩:=canonical_real_coefficient_bounds P
  obtain ⟨X₀,hX₀,hXbound⟩:=scalar_corrections_abs_uniform P
  let X:=max 1 X₀
  have hX:0<X:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let B':=2*max B δ₀⁻¹
  have hB':0<B':=by dsimp[B'];positivity
  refine ⟨2*(X+C),B',M₀,by positivity,hB',hM₀,?_⟩
  intro M hMscale
  have hM:2 ≤ M:=hM₀.trans hMscale
  have hcoef (j:ℕ) (d:List ℕ) (hd:1 ≤ d.length) (Y:ℝ) (hY:Y∈Set.Icc (0:ℝ) y₀) :
      |profileCoefficient P Y d j| ≤ C*B^j*profileOrderWeight (M:ℝ) j d^(2*j):=by
    apply (hcoef₀ j d hd Y hY).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by unfold profileOrderWeight;positivity)
    have hm:=mul_le_mul_of_nonneg_right (show (M₀:ℝ) ≤ M by exact_mod_cast hMscale)
      (Nat.cast_nonneg j : (0:ℝ) ≤ j)
    unfold profileOrderWeight
    linarith
  have hscalar (j p:ℕ) (hp:1 ≤ p) (Y:ℝ) (hY:Y∈Set.Icc (0:ℝ) y₀) :
      |cuspCoefficient P Y p j|+|genusCoefficient P Y p j| ≤
        C*B^j*scalarOrderWeight (M:ℝ) j p^(2*j):=by
    apply (hscalar₀ j p hp Y hY).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by unfold scalarOrderWeight;positivity)
    have hm:=mul_le_mul_of_nonneg_right (show (M₀:ℝ) ≤ M by exact_mod_cast hMscale)
      (Nat.cast_nonneg j : (0:ℝ) ≤ j)
    unfold scalarOrderWeight
    linarith
  constructor
  · intro g d hd hs hh L hL Y hY hδ
    have hhR:(0:ℝ)<complexity g d.length:=by exact_mod_cast (show 0<complexity g d.length by omega)
    have hp:|profile P g d Y| ≤ X:=by
      obtain ⟨hn,hp⟩:=(profile_monotone P g d hs 0 (by omega) Y hY).2
      rw[abs_of_nonneg hn]
      exact hp.trans (le_max_left _ _)
    have hg:=finite_expansion_large_weight_bound (profile P g d Y)
      (fun j=>profileCoefficient P Y d j/(complexity g d.length:ℝ)^j) L
      X C B δ₀ (profileOrderWeight (M:ℝ) L d^2/(complexity g d.length:ℝ))
      hX.le hC.le hB.le hδ₀ hδ hp
      (fun j hj=>profile_truncation_term_bound P Y d C B (M:ℝ) _ L j hC.le hB.le
        (Nat.cast_nonneg _) hhR hj.le (hcoef j d hd Y hY))
    have hhg:(X+C)*B'^L*(profileOrderWeight (M:ℝ) L d^2/(complexity g d.length:ℝ))^L ≤
        (2*(X+C))*B'^L*(profileOrderWeight (M:ℝ) L d^2/(complexity g d.length:ℝ))^L:=by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hB'.le _)
      · positivity
    exact (hg.trans hhg).trans_eq (by rw[div_pow,←pow_mul];ring)
  · intro g p hp hs hh L hL Y hY hδ
    have hhR:(0:ℝ)<complexity g p:=by exact_mod_cast (show 0<complexity g p by omega)
    have hx:=hXbound g p hp hs Y hY
    have hcX:|cuspCorrection P g p Y| ≤ X:=
      (le_add_of_nonneg_right (abs_nonneg _)).trans (hx.trans (le_max_right _ _))
    have hgX:|genusCorrection P g p Y| ≤ X:=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (hx.trans (le_max_right _ _))
    have hcCoef (j:ℕ):|cuspCoefficient P Y p j| ≤ C*B^j*scalarOrderWeight (M:ℝ) j p^(2*j):=
      (le_add_of_nonneg_right (abs_nonneg _)).trans (hscalar j p hp Y hY)
    have hgCoef (j:ℕ):|genusCoefficient P Y p j| ≤ C*B^j*scalarOrderWeight (M:ℝ) j p^(2*j):=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (hscalar j p hp Y hY)
    have hc:=finite_expansion_large_weight_bound (cuspCorrection P g p Y)
      (fun j=>cuspCoefficient P Y p j/(complexity g p:ℝ)^j) L
      X C B δ₀ (scalarOrderWeight (M:ℝ) L p^2/(complexity g p:ℝ))
      hX.le hC.le hB.le hδ₀ hδ hcX
      (fun j hj=>scalar_truncation_term_bound _ C B (M:ℝ) _ p L j hC.le hB.le
        (Nat.cast_nonneg _) hhR hj.le (hcCoef j))
    have hg:=finite_expansion_large_weight_bound (genusCorrection P g p Y)
      (fun j=>genusCoefficient P Y p j/(complexity g p:ℝ)^j) L
      X C B δ₀ (scalarOrderWeight (M:ℝ) L p^2/(complexity g p:ℝ))
      hX.le hC.le hB.le hδ₀ hδ hgX
      (fun j hj=>scalar_truncation_term_bound _ C B (M:ℝ) _ p L j hC.le hB.le
        (Nat.cast_nonneg _) hhR hj.le (hgCoef j))
    exact (add_le_add hc hg).trans_eq (by rw[div_pow,←pow_mul];dsimp[B'];ring)
end WP.HigherOrder
