import WPFormalization.Tight.ConnectedOrbitMoments

/-! The same actual connected tuple count on the original all-cusp moduli
space and the original WP probability measure. Only the previously proved
identity transport of the empty-protected-boundary presentation is used. -/
noncomputable section
namespace WP.TightConnected
open Set Filter Finset MeasureTheory External
open scoped Topology BigOperators ENNReal

def connectedCuspWindowCount {P : PsiTheory} {G : WeilPeterssonGeometry P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry G}
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology G T H Q)
    (g k n : ℕ) (I : Fin k → Set ℝ) (X : G.Moduli g n (fun _ => 0)) : ℕ :=
  connectedScaledWindowCount Q A g k n I ((tightCuspMeasurableEquiv G g n).symm X)

lemma connected_cusp_window_count_expectation_eq {P : PsiTheory}
    {G : WeilPeterssonGeometry P} {T : TightRegions G} {H : HyperbolicCurveGeometry G}
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology G T H Q)
    (g k n : ℕ) (I : Fin k → Set ℝ) :
    (∫⁻ X, (connectedCuspWindowCount Q A g k n I X : ℝ≥0∞) ∂wpProbability G g n) =
      ∫⁻ X, (connectedScaledWindowCount Q A g k n I X : ℝ≥0∞)
        ∂connectedCuspProbability G g n := by
  rw [MeasurePreserving.lintegral_map_equiv _ (tightCuspMeasurableEquiv G g n)
    (connected_cusp_probability_measurePreserving G g n)]
  simp [connectedCuspWindowCount]

lemma connected_cusp_window_count_expectation_tendsto {P : PsiTheory}
    {G : WeilPeterssonGeometry P} (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    {H : HyperbolicCurveGeometry G} (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (k : ℕ) (gs ns : ℕ → ℕ) (hgs : Tendsto gs atTop atTop)
    (I : Fin k → Set ℝ) (hI : ∀ i, MeasurableSet (I i))
    (B : ℝ) (hB : 0 ≤ B) (hIB : ∀ i, I i ⊆ Icc (0 : ℝ) B) :
    Tendsto (fun j => ∫⁻ X, (connectedCuspWindowCount Q A (gs j) k (ns j) I X : ℝ≥0∞)
      ∂wpProbability G (gs j) (ns j)) atTop (𝓝 (∏ i, tightIntensity (I i))) := by
  apply (connected_scaled_window_count_expectation_tendsto_intensity
    T BZ Q A MI k gs ns hgs I hI B hB hIB).congr'
  exact Eventually.of_forall fun j =>
    (connected_cusp_window_count_expectation_eq Q A (gs j) k (ns j) I).symm

end WP.TightConnected
