import WPFormalization.Comparison.LinearChildren
import WPFormalization.Comparison.LinearLower
import WPFormalization.Comparison.StateLowerBounds
import WPFormalization.Comparison.FiniteBarrier
/-! The complete lower harmonic comparison from the actual finite recursion.
The parameter belongs to the state, so the constants are uniform in Y.
The genuine typed children satisfy the proved mass, zero-potential and
superaveraging bounds; the finite-rank survival barrier then proves the
original logarithmic exponent without an additional probability assumption. -/
noncomputable section
namespace WP.ComparisonState
open Set
lemma linearLayerWeight_eq_coef (x:ComparisonState)(Y:ℝ)(l:ℕ):
    x.linearLayerWeight Y l=linearLowerCoef Y x.genus x.pivot x.tail l := by
  simp only[linearLayerWeight,linearDeficit,linearLowerCoef,x.rank_pivot]
lemma linear_weight_mass_eq (x:ComparisonState)(Y:ℝ)(hx:¬x.terminal):
    (∑i:x.linearIndex,x.linearWeight Y i)=linearRawMass Y x.genus x.pivot x.tail := by
  rw[linearRawMass_eq_nested]
  have he:=linear_sum_flatten Y x hx (fun _ _=>(1:ℝ))
  simpa only[mul_one,linearLayerWeight_eq_coef,linearDeficit] using he
lemma linear_weight_potential_eq (x:ComparisonState)(Y:ℝ)(hx:¬x.terminal):
    (∑i:x.linearIndex,x.linearWeight Y i*(2:ℝ)^((x.linearChild i).zeroCount))=
      linearRawPotential Y x.genus x.pivot x.tail := by
  rw[linearRawPotential_eq_nested]
  have he:=linear_sum_flatten Y x hx (fun _ d=>(2:ℝ)^(zeros d))
  simpa only[zeroCount,linearLayerWeight_eq_coef,linearDeficit] using he
lemma linear_weight_subaverage (x:ComparisonState)(P:PsiTheory)(Y:ℝ)(hY:Y∈Icc 0 y₀)(hx:¬x.terminal):
    (∑i:x.linearIndex,x.linearWeight Y i*ratio P (x.linearChild i).genus (x.linearChild i).degrees Y) ≤
      ratio P x.genus x.degrees Y := by
  rw[linear_sum_flatten Y x hx (fun g d=>ratio P g d Y),x.pivot_ratio P Y]
  have he:=linear_ratio_subaveraging P Y x.genus x.pivot x.tail (x.nonterminal_genus hx) x.pivot_admissible hY
  simpa only[linearLayerWeight_eq_coef,linearLowerCoef,linearDeficit] using he
lemma linear_weight_mass_lower (x:ComparisonState)(Y:ℝ)(hY:Y∈Icc 0 y₀)(hx:¬x.terminal):
    Real.exp (-(x.zeroCount:ℝ)/(x.rank:ℝ)) ≤ ∑i:x.linearIndex,x.linearWeight Y i := by
  rw[x.linear_weight_mass_eq Y hx]
  exact x.mass_exp_lower Y hY hx
lemma linear_weight_potential_bound (x:ComparisonState)(Y:ℝ)(hY:Y∈Icc 0 y₀)(hx:¬x.terminal):
    (∑i:x.linearIndex,x.linearWeight Y i*(2:ℝ)^((x.linearChild i).zeroCount)) ≤
      (∑i:x.linearIndex,x.linearWeight Y i)*((2:ℝ)^(x.zeroCount)+(2:ℝ)^26) := by
  rw[x.linear_weight_mass_eq Y hx,x.linear_weight_potential_eq Y hx]
  exact x.potential_bound Y hY hx
end WP.ComparisonState
namespace WP
open Set
theorem comparison_lower_proof (P : PsiTheory) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ g : ℕ, ∀ d : List ℕ, 1  ≤  d.length → Stable g d.length →
    d.sum  ≤  dimension g d.length → ∀ Y ∈ Set.Icc 0 y₀,
      c*Real.exp (-C*(zeros d+Real.log (complexity g d.length+1))*
        Real.log (complexity g d.length+1))  ≤  ratio P g d Y  := by
  obtain ⟨ct,Ct,hct,hCt,hterminal⟩:=ComparisonState.terminal_lower_uniform P
  let α:=Icc (0:ℝ) y₀ × ComparisonState
  let R:α→ℝ:=fun a=>ratio P a.2.genus a.2.degrees a.1
  let child:∀a:α,a.2.linearIndex→α:=fun a i=>(a.1,a.2.linearChild i)
  obtain ⟨c,C,hc,hC,hbound⟩:=Analysis.finite_rank_log_lower
    (fun a:α=>a.2.linearIndex) (fun a:α=>a.2.rank) (fun a:α=>a.2.zeroCount)
    R (fun a:α=>a.2.terminal) child (fun a:α=>a.2.linearWeight a.1)
    ct Ct hct hCt.le
    (fun a=>a.2.rank_pos)
    (fun a=>a.2.ratio_nonneg P a.1 a.1.property)
    (fun a ht=>hterminal a.1 a.1.property a.2 ht)
    (fun a ht=>a.2.nonterminal_rank ht)
    (fun a i _=>ComparisonState.linearWeight_nonneg a.1 a.1.property a.2 i)
    (fun a ht i _ hwi=>ComparisonState.linearChild_rank a.1 a.2 ht i hwi)
    (fun a ht=>a.2.linear_weight_mass_lower a.1 a.1.property ht)
    (fun a ht=>a.2.linear_weight_potential_bound a.1 a.1.property ht)
    (fun a ht=>a.2.linear_weight_subaverage P a.1 a.1.property ht)
  refine ⟨c,C,hc,hC,?_⟩
  intro g d hn hs hd Y hY
  exact hbound (⟨Y,hY⟩,⟨(g,d),hn,hs,hd⟩)
end WP
