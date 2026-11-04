import Mathlib
/-! A uniform two-regime assembly. Bounded cusp counts and every jointly
divergent genus/cusp sequence cover all cusp counts, with one genus threshold. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology

lemma uniform_of_bounded_counts_and_sequential {α:Type*}
    (E:ℕ→ℕ→α→ℝ)(C:α→Prop)
    (hb:∀N:ℕ,∀ε:ℝ,0<ε→∃G:ℕ,∀g≥G,∀q≤N,∀a,C a→|E g q a|≤ε)
    (hs:∀(gs qs:ℕ→ℕ)(as:ℕ→α),Tendsto gs atTop atTop→Tendsto qs atTop atTop→
      (∀j,C (as j))→Tendsto (fun j=>E (gs j) (qs j) (as j)) atTop (𝓝 0)) :
    ∀ε:ℝ,0<ε→∃G:ℕ,∀g≥G,∀q:ℕ,∀a,C a→|E g q a|≤ε := by
  classical
  intro ε hε
  by_contra hn
  push_neg at hn
  choose B hB using fun j=>hb j ε hε
  have hbad (j:ℕ) : ∃g:ℕ,max j (B j)≤g ∧ ∃q:ℕ,∃a:α,C a ∧ ε < |E g q a| :=
    hn (max j (B j))
  choose gs hg qs as ha he using hbad
  have hg' (j:ℕ):j≤gs j := (le_max_left _ _).trans (hg j)
  have hq (j:ℕ):j≤qs j := by
    by_contra h
    have hsmall:qs j≤j:=by omega
    have hb':|E (gs j) (qs j) (as j)|≤ε:=
      hB j (gs j) ((le_max_right _ _).trans (hg j)) (qs j) hsmall (as j) (ha j)
    linarith [he j]
  have hgs:Tendsto gs atTop atTop:=tendsto_atTop_mono hg' tendsto_id
  have hqs:Tendsto qs atTop atTop:=tendsto_atTop_mono hq tendsto_id
  have ht:=hs gs qs as hgs hqs ha
  have hav:∀ᶠj:ℕ in atTop,|E (gs j) (qs j) (as j)|<ε:=by
    simpa only [Real.dist_eq,sub_zero] using (Metric.tendsto_nhds.mp ht ε hε)
  obtain ⟨j,hj⟩:=hav.exists
  linarith [he j]

end WP.BoundaryConvolution
