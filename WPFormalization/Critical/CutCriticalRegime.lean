import WPFormalization.Critical.CutActualEstimate
noncomputable section
namespace WP.Critical
open Filter
lemma critical_cusp_regime_eventually (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ g : ℕ in atTop,
      1 ≤ n g ∧ (n g : ℝ) ≤ A*Real.sqrt g := by
  refine ⟨c+1,by linarith,?_⟩
  have hu : ∀ᶠ g : ℕ in atTop, (n g : ℝ)/Real.sqrt g < c+1 :=
    hn.eventually (Iio_mem_nhds (by linarith))
  have hl : ∀ᶠ g : ℕ in atTop, 0 < (n g : ℝ)/Real.sqrt g :=
    hn.eventually (Ioi_mem_nhds hc)
  filter_upwards [hu,hl,eventually_ge_atTop 1] with g hgu hgl hg
  have hs : 0 < Real.sqrt (g : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hg)
  have hnpos : 0 < (n g : ℝ) := (div_pos_iff_of_pos_right hs).mp hgl
  refine ⟨by exact_mod_cast (by exact_mod_cast hnpos : 0 < n g),?_⟩
  exact ((div_lt_iff₀ hs).mp hgu).le
end WP.Critical

namespace WP.Critical
open WP.External Filter MeasureTheory CutGraphOrbits
open scoped ENNReal
universe aa bb cc dd

/- The original critical sequence formulation of Lemma G.1. -/
@[blueprint "lem:critical-cuts"]
theorem critical_cut_estimate_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, cutPartitionCount T S (g:=g) (n:=n g) u v w L X ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2)) := by
  obtain ⟨A,hA,hregime⟩ := critical_cusp_regime_eventually n c hc hn
  obtain ⟨C,hC,G₀,hr⟩ := critical_cut_estimate G T MI k Q u v w hk hQ A L hA hL
  refine ⟨C,hC,?_⟩
  filter_upwards [hregime,eventually_ge_atTop G₀] with g hg hG
  exact hr g hG (n g) hg.1 hg.2

/- The original marked-leaf critical sequence formulation of Lemma G.1. -/
@[blueprint "lem:critical-cuts"]
theorem critical_cut_marked_estimate_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, cutMarkedPartitionCount T S (g:=g) (n:=n g) u v w L X ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2)) := by
  obtain ⟨A,hA,hregime⟩ := critical_cusp_regime_eventually n c hc hn
  obtain ⟨C,hC,G₀,hr⟩ := critical_cut_marked_estimate G T MI k Q u v w hk hQ A L hA hL
  refine ⟨C,hC,?_⟩
  filter_upwards [hregime,eventually_ge_atTop G₀] with g hg hG
  exact hr g hG (n g) hg.1 hg.2
end WP.Critical
