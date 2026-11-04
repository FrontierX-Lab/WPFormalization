import WPFormalization.Critical.CutUnorderedCount
import WPFormalization.Critical.CutCriticalRegime

noncomputable section
namespace WP.Critical
open WP.External CutGraphOrbits MeasureTheory Filter
open scoped ENNReal
universe aa bb cc dd

/- Lemma G.1 for unordered finite sets of actual geometric primitive curves. -/
@[blueprint "lem:critical-cuts"]
theorem critical_unordered_cut_estimate {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (partitionOrbits T S (g:=g) (n:=n) u v w) L X
        ∂wpProbability G g n) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2)) := by
  obtain ⟨C,hC,G₀,hr⟩ := critical_cut_estimate G T MI k Q u v w hk hQ A L hA hL
  refine ⟨C,hC,G₀,?_⟩
  intro g hg n hn hcritical S hS
  exact (lintegral_mono (fun X => unorderedCutCount_le_ordered T _ L X)).trans
    (hr g hg n hn hcritical S hS)

/- The marked-leaf part of Lemma G.1 for the actual unordered cut count. -/
@[blueprint "lem:critical-cuts"]
theorem critical_unordered_cut_marked_estimate {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (markedPartitionOrbits T S (g:=g) (n:=n) u v w) L X
        ∂wpProbability G g n) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2)) := by
  obtain ⟨C,hC,G₀,hr⟩ := critical_cut_marked_estimate G T MI k Q u v w hk hQ A L hA hL
  refine ⟨C,hC,G₀,?_⟩
  intro g hg n hn hcritical S hS
  exact (lintegral_mono (fun X => unorderedCutCount_le_ordered T _ L X)).trans
    (hr g hg n hn hcritical S hS)

/- The exact original n/sqrt(g) -> c>0 regime for the unordered cut count. -/
@[blueprint "lem:critical-cuts"]
theorem critical_unordered_cut_estimate_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (partitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2)) := by
  obtain ⟨A,hA,hregime⟩ := critical_cusp_regime_eventually n c hc hn
  obtain ⟨C,hC,G₀,hr⟩ := critical_unordered_cut_estimate G T MI k Q u v w hk hQ A L hA hL
  refine ⟨C,hC,?_⟩
  filter_upwards [hregime,eventually_ge_atTop G₀] with g hg hG
  exact hr g hG (n g) hg.1 hg.2

/- The designated three-cusp leaf in the original regime gains g^(-1/2). -/
@[blueprint "lem:critical-cuts"]
theorem critical_unordered_cut_marked_estimate_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (markedPartitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2)) := by
  obtain ⟨A,hA,hregime⟩ := critical_cusp_regime_eventually n c hc hn
  obtain ⟨C,hC,G₀,hr⟩ := critical_unordered_cut_marked_estimate G T MI k Q u v w hk hQ A L hA hL
  refine ⟨C,hC,?_⟩
  filter_upwards [hregime,eventually_ge_atTop G₀] with g hg hG
  exact hr g hG (n g) hg.1 hg.2
end WP.Critical
