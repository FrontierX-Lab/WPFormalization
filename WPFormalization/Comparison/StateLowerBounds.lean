import WPFormalization.Comparison.TypedStates
import WPFormalization.Comparison.LinearMassLower
/-! Uniform terminal and transition bounds for the genuine typed comparison
states. These use the actual PI/terminal estimates and genuine zero-count
linear kernel, retaining uniformity over the closed parameter interval. -/
noncomputable section
namespace WP.ComparisonState
open Set
lemma lower_choice (x:ComparisonState):1 ≤ x.pivot ∨(x.pivot=0 ∧∀k∈x.tail,k=0) := by
  rcases x.pivot_choice with hp|hp
  · exact Or.inl (by omega)
  · exact Or.inr hp
lemma nonterminal_rank (x:ComparisonState)(hx:¬x.terminal):2 ≤ x.rank := by
  have hg:=x.nonterminal_genus hx
  unfold rank complexity
  omega
lemma ratio_nonneg (x:ComparisonState)(P:PsiTheory)(Y:ℝ)(hY:Y∈Icc 0 y₀):
    0 ≤ ratio P x.genus x.degrees Y :=
  div_nonneg (normalized_nonneg_nonempty P x.genus x.degrees x.nonempty Y hY)
    (model_pos x.genus x.degrees Y x.stable hY).le
lemma terminal_lower_uniform (P:PsiTheory):∃c Ct:ℝ,0<c ∧0<Ct ∧∀Y∈Icc (0:ℝ) y₀,∀x:ComparisonState,
    x.terminal→c*Real.exp (-Ct*(x.zeroCount:ℝ)) ≤ ratio P x.genus x.degrees Y := by
  obtain ⟨c,Ct,hc,hCt,hterm⟩:=terminal_ratio_lower P
  refine ⟨c,Ct,hc,hCt,?_⟩
  intro Y hY x ht
  have he:=hterm x.genus x.degrees x.nonempty x.stable x.admissible Y hY ht
  simpa only[zeroCount,zeros,←count_zero_filter_length] using he
lemma mass_exp_lower (x:ComparisonState)(Y:ℝ)(hY:Y∈Icc 0 y₀)(hx:¬x.terminal):
    Real.exp (-(x.zeroCount:ℝ)/(x.rank:ℝ)) ≤ linearRawMass Y x.genus x.pivot x.tail := by
  have he:=linearRawMass_exp_lower Y hY x.genus x.pivot x.tail (x.nonterminal_genus hx)
    x.pivot_admissible x.lower_choice
  simpa only[x.pivot_zeros,x.rank_pivot] using he
lemma potential_bound (x:ComparisonState)(Y:ℝ)(hY:Y∈Icc 0 y₀)(hx:¬x.terminal):
    linearRawPotential Y x.genus x.pivot x.tail ≤ linearRawMass Y x.genus x.pivot x.tail*
      ((2:ℝ)^(x.zeroCount)+(2:ℝ)^26) := by
  have he:=linearRawPotential_bound Y hY x.genus x.pivot x.tail (x.nonterminal_genus hx) x.lower_choice
  simpa only[x.pivot_zeros] using he
end WP.ComparisonState
