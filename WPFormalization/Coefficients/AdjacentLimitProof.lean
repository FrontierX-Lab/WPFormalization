import WPFormalization.Statements.QuantitativeAdjacent
/-! The original all-degree uniform limit is a direct consequence of the proved quantitative theorem. -/
set_option autoImplicit false
noncomputable section
namespace WP
open Filter
open scoped Topology
lemma adjacent_limit_proof (P : PsiTheory) :
    ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ, k < 3*g-2 →
      adjacentError P g k ≤ ε :=by
  obtain ⟨C,hC,G,hb⟩:=(quantitative_adjacent P).1
  have ht:Tendsto (fun g:ℕ=>C*(g:ℝ)^(-1/8:ℝ)) atTop (𝓝 (0:ℝ)):=by
    have H: Tendsto (fun g:ℕ=>(g:ℝ)^(-1/8:ℝ)) atTop (𝓝 (0:ℝ)):=
      by simpa only[Function.comp_def,neg_div,Real.rpow_eq_pow] using (tendsto_rpow_neg_atTop (by norm_num:(0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop
    simpa only[mul_zero] using H.const_mul C
  intro ε hε
  obtain ⟨G1,hG1⟩:=eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨max G G1,?_⟩
  intro g hg k hk
  exact (hb g ((le_max_left _ _).trans hg) k hk).trans
    (hG1 g ((le_max_right _ _).trans hg)).le
end WP
