import WPFormalization.Tight.SeparatingExpectation
import WPFormalization.Tight.SpectrumTupleExtensionsTransport

/- Original Lemma F.3 on the same actual cusp moduli and normalized WP measure.
The canonical index equivalence transports precisely the finite ordered
primitive simple disjoint separating tuples. Both the nonnegative integral and
the real expectation are uniform over every cusp count, including zero. -/
noncomputable section
universe u v w z
namespace WP.TightSeparating
open Set Filter Finset MeasureTheory External
open scoped Topology BigOperators ENNReal

lemma tightPrefixWpProbability_measurePreserving {P : PsiTheory}
    (G : WeilPeterssonGeometry.{u,v} P) (g n : ℕ) (hs : Stable g n) :
    MeasurePreserving (tightCuspMeasurableEquiv G g n)
      (tightPrefixWpProbability G g n) (wpProbability G g n) := by
  have hm : ENNReal.ofReal (cuspVolume G g n) = G.wpMeasure g n (fun _ => 0) univ := by
    unfold cuspVolume wpVolume
    exact ENNReal.ofReal_toReal (G.finite_volume g n _ hs (fun _ => le_rfl))
  unfold tightPrefixWpProbability
  rw [hm]
  exact tightCuspMeasurableEquiv_wpProbability G g n

def actualTightSeparatingCount {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    {g n : ℕ} (k : ℕ) (ell : ℝ) (X : G.Moduli g n (fun _ => 0)) : ℕ :=
  tightSeparatingCount Q A k ell ((tightCuspMeasurableEquiv G g n).symm X)

@[blueprint "lem:tight-separating"]
theorem actual_tight_separating_expectation_uniform {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (BZ : BuddZonneveldTransform G T) (I : BuddLionsTightIntegration G T H Q A)
    (k : ℕ) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g ≥ N, ∀ n : ℕ,
      Integrable (fun X => (actualTightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ))
        (wpProbability G g n) ∧
      (∫ X : G.Moduli g n (fun _ => 0),
        (actualTightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ)
        ∂wpProbability G g n) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := tight_separating_expectation_real_uniform T A BZ I k L0 hL0 ε hε
  refine ⟨max N 2,?_⟩
  intro g hg n
  have hs : Stable g n := by unfold Stable;omega
  have mp := tightPrefixWpProbability_measurePreserving G g n hs
  have hb := hN g (le_of_max_le_left hg) n
  have hint : (∫ X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0),
        (tightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ)
        ∂tightPrefixWpProbability G g n) =
      (∫ X : G.Moduli g n (fun _ => 0),
        (actualTightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ)
        ∂wpProbability G g n) := by
    simpa only [actualTightSeparatingCount,MeasurableEquiv.symm_apply_apply] using
      mp.integral_comp' (fun X =>
        (actualTightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ))
  refine ⟨?_,by rw [←hint];exact hb.2⟩
  apply (mp.integrable_comp_emb (tightCuspMeasurableEquiv G g n).measurableEmbedding).mp
  simpa only [actualTightSeparatingCount,Function.comp_def,MeasurableEquiv.symm_apply_apply] using hb.1



@[blueprint "lem:tight-separating"]
theorem actual_tight_separating_lintegral_uniform {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (BZ : BuddZonneveldTransform G T) (I : BuddLionsTightIntegration G T H Q A)
    (k : ℕ) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g ≥ N, ∀ n : ℕ,
      (∫⁻ X : G.Moduli g n (fun _ => 0),
        (actualTightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ≥0∞)
        ∂wpProbability G g n) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := tight_separating_expectation_uniform T A BZ I k L0 hL0 ε hε
  refine ⟨max N 2,?_⟩
  intro g hg n
  have hs : Stable g n := by unfold Stable;omega
  have mp := tightPrefixWpProbability_measurePreserving G g n hs
  have he := mp.lintegral_comp_emb (tightCuspMeasurableEquiv G g n).measurableEmbedding
    (fun X => (actualTightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ≥0∞))
  simp only [actualTightSeparatingCount,MeasurableEquiv.symm_apply_apply] at he
  unfold actualTightSeparatingCount
  rw [←he]
  exact hN g (le_of_max_le_left hg) n

end WP.TightSeparating
