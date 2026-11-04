import WPFormalization.External.MirzakhaniIntegration

/-! Classical Borel measurability for actual finite families of unordered
geometric multicurves. This is the standard measurable-count ingredient in
Mirzakhani's 2007 integration setup: marked curve classes are countable and
geodesic lengths are continuous on Teichmuller space; the counting observable
descends through the mapping-class quotient. The exact generic interface is
an explicit phase-one classical parameter. It contains no estimate, volume
comparison, graph restriction, or limit, and no instance is postulated. -/
noncomputable section
universe aa bb cc dd
namespace WP.External
open MeasureTheory
open scoped ENNReal Classical
namespace MulticurveTopology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)

def unorderedLengthCount {g n k : ℕ} (s : Finset (T.Orbit g n k))
    (B : Set (Fin k → ℝ)) (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑' U : {U : Finset (H.Primitive g n X) //
    ∃ o ∈ s, ∃ γ : Fin k → H.Primitive g n X,
      T.orbitMem o X γ ∧ Finset.univ.image γ=U ∧ (fun i => H.length (γ i)) ∈ B}, (1 : ℝ≥0∞)
end MulticurveTopology

/-- Classical Borel measurability of finite families of geometric multicurve
counts, before any volume estimate, genus limit, or probabilistic asymptotic. -/
structure MulticurveCountingMeasurability {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) (H : HyperbolicCurveGeometry.{aa,bb,cc} G)
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) : Prop where
  unorderedLengthCount_measurable : ∀ {g n k : ℕ} (s : Finset (T.Orbit g n k))
    (B : Set (Fin k → ℝ)), MeasurableSet B → IsCompact (closure B) →
      Measurable (T.unorderedLengthCount s B)
end WP.External
