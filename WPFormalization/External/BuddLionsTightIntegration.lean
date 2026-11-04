import WPFormalization.External.TightMulticurveTopology

/- Exact classical orbit integration, Budd--Lions arXiv:2506.02611v3,
Proposition 3.2 (pp.13--17), using the SAME actual WP measure and tightVolume.
The coefficient is the source orbifold coefficient, bounded by one and exactly
2^(-r) for connected complement; it is never chosen to fit an asymptotic.
Phase two must prove the cut/twist symplectic integration and measurability.
No prescribed-cusp coefficient estimate, F.2/F.3 bound, or probability limit is
assumed here. -/
noncomputable section
universe u v w z
namespace WP.External
open Set MeasureTheory
open scoped ENNReal

/- BL v3 Proposition 3.2, PDF pp.13-17. The finite labeled assignment sum
is exact; no coefficient-extraction estimate or large-genus field occurs. -/
@[blueprint "ext:tight-integration"]
structure BuddLionsTightIntegration {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (T : TightRegions G) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology G T H Q) where
  coefficient : ∀ {g p r}, A.Orbit g p r → ℝ≥0∞
  coefficient_pos : ∀ {g p r} (o : A.Orbit g p r), 0 < coefficient o
  coefficient_le_one : ∀ {g p r} (o : A.Orbit g p r), coefficient o ≤ 1
  coefficient_connected : ∀ {g p r} (o : A.Orbit g p r), (A.cut o).components = 1 →
    coefficient o = ((2 : ℝ≥0∞)^r)⁻¹
  orbitSum_measurable : ∀ {g p r k} (o : A.Orbit g p r) (L : Fin p → ℝ) (K : Fin k → ℝ)
    (F : (Fin r → ℝ) → ℝ≥0∞), Measurable F → Measurable (A.orbitSum o F (L:=L) (K:=K))
  cutKernel_measurable : ∀ {g p r k} (o : A.Orbit g p r) (L : Fin p → ℝ) (K : Fin k → ℝ),
    Measurable (fun x => (A.cut o).tightCutKernel T L K x)
  orbit_integral : ∀ {g p r k} (o : A.Orbit g p r), Stable g p →
    ∀ (L : Fin p → ℝ) (K : Fin k → ℝ), (∀ i, 0 ≤ L i) → (∀ i, 0 ≤ K i) →
    ∀ (F : (Fin r → ℝ) → ℝ≥0∞), Measurable F →
    (∫⁻ X in T.region g p k L K, A.orbitSum o F X ∂G.wpMeasure g (p+k) (Fin.append L K)) =
      coefficient o * ∫⁻ x : Fin r → ℝ in {x | ∀ i, 0 ≤ x i},
        F x * ENNReal.ofReal ((A.cut o).tightCutKernel T L K x) * ∏ i, ENNReal.ofReal (x i)

end WP.External
