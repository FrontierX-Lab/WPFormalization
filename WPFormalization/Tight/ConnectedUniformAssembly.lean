import WPFormalization.Volumes.BoundaryUniformAssembly
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

/-- Fixed-index sequential convergence uniform over an auxiliary compact box,
combined with joint divergence, gives one threshold for all indices. -/
lemma connected_uniform_of_fixed_and_diverging {α:Type*}
    (E:ℕ→ℕ→α→ℝ) (C:α→Prop)
    (hfixed:∀n:ℕ,∀(gs:ℕ→ℕ)(as:ℕ→α),Tendsto gs atTop atTop→
      (∀j,C (as j))→Tendsto (fun j=>E (gs j) n (as j)) atTop (𝓝 0))
    (hdiv:∀(gs ns:ℕ→ℕ)(as:ℕ→α),Tendsto gs atTop atTop→Tendsto ns atTop atTop→
      (∀j,C (as j))→Tendsto (fun j=>E (gs j) (ns j) (as j)) atTop (𝓝 0)) :
    ∀ε:ℝ,0<ε→∃G:ℕ,∀g≥G,∀n:ℕ,∀a,C a→|E g n a|≤ε := by
  classical
  have hfixed_uniform : ∀n:ℕ,∀ε:ℝ,0<ε→∃G:ℕ,∀g≥G,∀a,C a→|E g n a|≤ε := by
    intro n ε hε
    by_contra hh
    push_neg at hh
    choose gs hgs as hC he using hh
    have hg : Tendsto gs atTop atTop := tendsto_atTop_mono hgs tendsto_id
    have ht := hfixed n gs as hg hC
    have hav : ∀ᶠj:ℕ in atTop,|E (gs j) n (as j)|<ε := by
      simpa only [Real.dist_eq,sub_zero] using Metric.tendsto_nhds.mp ht ε hε
    obtain ⟨j,hj⟩ := hav.exists
    linarith [he j]
  apply BoundaryConvolution.uniform_of_bounded_counts_and_sequential E C _ hdiv
  intro N ε hε
  choose G hG using fun n=>hfixed_uniform n ε hε
  refine ⟨(Finset.range (N+1)).sup G,?_⟩
  intro g hg n hn a ha
  have hle : G n≤(Finset.range (N+1)).sup G := Finset.le_sup (Finset.mem_range.mpr (by omega))
  exact hG n g (hle.trans hg) a ha
end WP.TightConnected
