import WPFormalization.HigherOrder.SmallWeightAlgebra
import WPFormalization.HigherOrder.FiniteRemainderAlgebra
import WPFormalization.HigherOrder.OrderWeights
import WPFormalization.Statements.GrowingMarkingFirstOrder
/-! The actual small-weight inversion domain in Appendix C.3.
One positive δ₀ works for every M≥2 and every child marking/complexity
shift used by the finite expansion. The genuine C.6 cusp estimate is
instantiated before asserting cusp≥1/2. Invalid degree tuples lie in the
large-weight region. The actual formal inverse has the exact finite
single-remainder bound, with no assumed remainder estimate. -/
noncomputable section
namespace WP.HigherOrder
lemma cusp_inverse_small_weight_uniform (P:PsiTheory) :
    ∃δ₀:ℝ,0<δ₀ ∧ δ₀ ≤ 1 ∧∀M h:ℝ,2 ≤ M→0<h→∀p L:ℕ,1 ≤ p→1 ≤ L→
    scalarOrderWeight M L p^2/h<δ₀→∀g q:ℕ,1 ≤ q→h-(L:ℝ) ≤ (complexity g q:ℝ)→
    q ≤ p+L+2→∀Y∈Set.Icc (0:ℝ) y₀,
      1/2 ≤ cuspCorrection P g q Y ∧ |(cuspCorrection P g q Y)⁻¹| ≤ 2 :=by
  obtain ⟨C,hC,H,hfirst⟩:=growing_marking_cusp_first_order_proof P 4 (by norm_num)
  obtain ⟨δ,hδ,hδ1,he⟩:=inverse_lower_from_uniform_first_order complexity (cuspCorrection P)
    (Set.Icc (0:ℝ) y₀) C hC H hfirst
  refine ⟨δ,hδ,hδ1,?_⟩
  intro M h hM hh p L hp hL hsmall g q hq hshift hqp Y hY
  apply he h (scalarOrderWeight M L p) hh p L hp hL _ hsmall g q hq hshift hqp Y hY
  have hm:=mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg L : (0:ℝ) ≤ L)
  unfold scalarOrderWeight
  linarith

lemma invalid_profile_large_weight (M:ℝ) (hM:0 ≤ M) (L g:ℕ) (d:List ℕ)
    (hh:1 ≤ complexity g d.length) (hd:dimension g d.length<d.sum) :
    1 ≤ profileOrderWeight M L d^2/(complexity g d.length:ℝ) :=by
  have hD:complexity g d.length ≤ d.sum:=by unfold complexity dimension at *;omega
  have hDR:(complexity g d.length:ℝ) ≤ d.sum:=by exact_mod_cast hD
  have hS:(complexity g d.length:ℝ) ≤ profileOrderWeight M L d:=by
    have hb:=profileOrderWeight_base_le M hM L d
    linarith [Nat.cast_nonneg (α:=ℝ) d.length]
  have hhR:(1:ℝ) ≤ complexity g d.length:=by exact_mod_cast hh
  apply (le_div_iff₀ (by linarith)).2
  nlinarith [sq_nonneg (profileOrderWeight M L d-(complexity g d.length:ℝ))]

lemma cusp_formal_inverse_remainder_bound (P:PsiTheory) (g p:ℕ) (Y t:ℝ)
    (hc:1/2 ≤ cuspCorrection P g p Y) (q:ℕ) (hq:1 ≤ q) :
    |(cuspCorrection P g p Y)⁻¹-truncationValue ((formalCusp P Y p)⁻¹) q t| ≤
      2*∑j∈Finset.range q,|PowerSeries.coeff j ((formalCusp P Y p)⁻¹)| *|t|^j*
        |cuspCorrection P g p Y-truncationValue (formalCusp P Y p) (q-j) t| :=by
  have hcp:0<cuspCorrection P g p Y:=by linarith
  have hinv:|(cuspCorrection P g p Y)⁻¹| ≤ 2:=by
    rw[abs_inv,abs_of_pos hcp]
    simpa only[one_div] using (one_div_le hcp (by norm_num:(0:ℝ)<2)).2 hc
  have hfd:formalCusp P Y p*(formalCusp P Y p)⁻¹=1:=
    PowerSeries.mul_inv_cancel _ (by simp)
  have hh:=exact_inverse_remainder_norm_le (cuspCorrection P g p Y) hcp.ne'
    (formalCusp P Y p) ((formalCusp P Y p)⁻¹) hfd q hq t
  simp only[Real.norm_eq_abs] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hinv (Finset.sum_nonneg (fun j hj=>by positivity)))
end WP.HigherOrder
