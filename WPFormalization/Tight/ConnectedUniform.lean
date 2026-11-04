import WPFormalization.Tight.ConnectedDensityDiverging
import WPFormalization.Tight.ConnectedPoissonDensity
import WPFormalization.Tight.ConnectedUniformAssembly
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

/-- Original connected-cut asymptotics on the equivalent density scale,
uniformly in every cusp count and a fixed compact box of scaled lengths.
Both original reference-saddle branches are proved separately. -/
lemma tight_connected_density_uniform (P:PsiTheory) (k:ℕ) (B:ℝ) (hB:0≤B) :
    ∀ε:ℝ,0<ε→∃G:ℕ,∀g≥G,∀n:ℕ,∀t:Fin (2*k)→ℝ,
      (∀i,t i∈Icc (0:ℝ) B)→|connectedDensityCoefficientRatio P k g n t-1|≤ε := by
  apply connected_uniform_of_fixed_and_diverging
    (fun g n t=>connectedDensityCoefficientRatio P k g n t-1) (fun t=>∀i,t i∈Icc (0:ℝ) B)
  · intro n gs ts hg ht
    have hr := connected_density_coefficient_ratio_bounded P k n 1 (by norm_num) B hB gs hg ts ht
    simpa only [sub_self] using hr.sub_const 1
  · intro gs ns ts hg hn ht
    have hr := connected_density_ratio_diverging P k B hB gs ns hg hn ts ht
    simpa only [sub_self] using hr.sub_const 1
end WP.TightConnected
