import WPFormalization.Tight.SeparatingExpectationRates
import WPFormalization.Tight.SpectrumTupleExtensionsOrbitSum

/- Actual ordered separating tuple counts and their prefix-index geometric WP expectation. The final original-index statement is transported in SeparatingActualExpectation. -/


noncomputable section
universe u v w z
namespace WP.TightSeparating
open Set Filter Finset MeasureTheory External TightMoments
open scoped Topology BigOperators ENNReal

def tightSeparatingCount {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    {g n : ℕ} (k : ℕ) (ell : ℝ)
    (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0)) : ℕ :=
  Nat.card {Γ : Fin k → Tight.SpectrumTupleExtensions.Curve Q X //
    Tight.SpectrumTupleExtensions.SeparatingTuple Q A X k ell Γ}

def tightPrefixWpProbability {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (g n : ℕ) : Measure (TightSurface G g 0 n (fun _ => 0) (fun _ => 0)) :=
  (ENNReal.ofReal (cuspVolume G g n))⁻¹ •
    G.wpMeasure g (0+n) (Fin.append (fun _ => 0) (fun _ => 0))

lemma separating_count_integral_eq_orbit {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (I : BuddLionsTightIntegration G T H Q A)
    (g k n : ℕ) (hg : Stable g 0) (ell : ℝ) :
    (∫⁻ X, (tightSeparatingCount Q A k ell X : ℝ≥0∞) ∂tightPrefixWpProbability G g n) =
      separatingOrbitIntegral T A g k n ell := by
  classical
  have he : (fun i : Fin 0 => (Fin.elim0 i : ℝ)) = (fun _ => 0) := by funext i;exact Fin.elim0 i
  have hreg : T.region g 0 n (fun _ => 0) (fun _ => 0) = univ := by
    ext X
    simp [TightRegions.region,tightLocus]
  unfold separatingOrbitIntegral
  rw [he]
  simp only [hreg,Measure.restrict_univ]
  rw [tightPrefixWpProbability,lintegral_smul_measure,smul_eq_mul]
  congr 1
  calc
    _ = ∫⁻ X, ∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter
        (fun o => 2 ≤ (A.cut o).components), A.orbitSum o (Critical.cutLengthTest k ell) X
          ∂G.wpMeasure g (0+n) (Fin.append (fun _ => 0) (fun _ => 0)) := by
      apply lintegral_congr
      intro X
      exact Tight.SpectrumTupleExtensions.separating_count_eq_orbit_sum Q A X k ell hg
    _ = _ := lintegral_finsetSum _ (fun o ho =>
      I.orbitSum_measurable o _ _ _ (Critical.cutLengthTest_measurable k ell))

theorem tight_separating_expectation_uniform {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (BZ : BuddZonneveldTransform G T) (I : BuddLionsTightIntegration G T H Q A)
    (k : ℕ) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g ≥ N, ∀ n : ℕ,
      (∫⁻ X, (tightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ≥0∞)
        ∂tightPrefixWpProbability G g n) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := tight_separating_orbit_uniform T A BZ I k L0 hL0 ε hε
  refine ⟨max N 2,?_⟩
  intro g hg n
  rw [separating_count_integral_eq_orbit T A I g k n (by unfold Stable;omega)]
  exact hN g (le_of_max_le_left hg) n


lemma tightSeparatingCount_measurable {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} {T : TightRegions G}
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (I : BuddLionsTightIntegration G T H Q A)
    (g k n : ℕ) (hg : Stable g 0) (ell : ℝ) :
    Measurable (fun X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) =>
      (tightSeparatingCount Q A k ell X : ℝ)) := by
  have hm : Measurable (fun X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) =>
      ∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter
        (fun o => 2 ≤ (A.cut o).components), A.orbitSum o (Critical.cutLengthTest k ell) X) :=
    Finset.measurable_sum _ (fun o _ => I.orbitSum_measurable o _ _ _
      (Critical.cutLengthTest_measurable k ell))
  have he : (fun X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) =>
      ∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter
        (fun o => 2 ≤ (A.cut o).components), A.orbitSum o (Critical.cutLengthTest k ell) X) =
      (fun X => (tightSeparatingCount Q A k ell X : ℝ≥0∞)) := by
    funext X
    exact (Tight.SpectrumTupleExtensions.separating_count_eq_orbit_sum Q A X k ell hg).symm
  rw [he] at hm
  simpa using hm.ennreal_toReal

lemma tight_separating_expectation_real_uniform {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (BZ : BuddZonneveldTransform G T) (I : BuddLionsTightIntegration G T H Q A)
    (k : ℕ) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g ≥ N, ∀ n : ℕ,
      Integrable (fun X => (tightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ))
        (tightPrefixWpProbability G g n) ∧
      (∫ X, (tightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ)
        ∂tightPrefixWpProbability G g n) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := tight_separating_expectation_uniform T A BZ I k L0 hL0 ε hε
  refine ⟨max N 2,?_⟩
  intro g hg n
  have hsg : Stable g 0 := by unfold Stable;omega
  have hm := tightSeparatingCount_measurable A I g k n hsg (L0/tightScale ((n : ℝ)/(g : ℝ)))
  have hnon : 0 ≤ᵐ[tightPrefixWpProbability G g n]
      (fun X => (tightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ)) :=
    Eventually.of_forall (fun X => Nat.cast_nonneg _)
  have hb := hN g (le_of_max_le_left hg) n
  constructor
  · refine ⟨hm.aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnon]
    simp only [ENNReal.ofReal_natCast]
    exact hb.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnon hm.aestronglyMeasurable]
    simp only [ENNReal.ofReal_natCast]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hε.le)

end WP.TightSeparating
