import WPFormalization.Critical.CutUnorderedMeasurable
import WPFormalization.Critical.CutUnorderedEstimate
noncomputable section
namespace WP.Critical
open WP.External CutGraphOrbits MeasureTheory Filter
open scoped ENNReal
universe aa bb cc dd

/- Lemma G.1 as a genuine expectation of a measurable actual unordered
multicurve count, with its classical measurable-count context explicit. -/
@[blueprint "lem:critical-cuts"]
theorem critical_cut_expectation_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (MC : MulticurveCountingMeasurability G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    (∀ (g : ℕ) (S : CutSkeleton k Q), Measurable
      (unorderedCutCount T (partitionOrbits T S (g:=g) (n:=n g) u v w) L)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (partitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2)) := by
  exact ⟨fun g S => unorderedCutCount_measurable T MC _ L,
    critical_unordered_cut_estimate_regime G T MI k Q u v w hk hQ L hL n c hc hn⟩

/- The same measurable expectation statement for a three-cusp designated leaf. -/
@[blueprint "lem:critical-cuts"]
theorem critical_cut_marked_expectation_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (MC : MulticurveCountingMeasurability G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    (∀ (g : ℕ) (S : CutSkeleton k Q), Measurable
      (unorderedCutCount T (markedPartitionOrbits T S (g:=g) (n:=n g) u v w) L)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (markedPartitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2)) := by
  exact ⟨fun g S => unorderedCutCount_measurable T MC _ L,
    critical_unordered_cut_marked_estimate_regime G T MI k Q u v w hk hQ L hL n c hc hn⟩
end WP.Critical
