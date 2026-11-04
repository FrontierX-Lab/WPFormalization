import WPFormalization.Tight.SpectrumTupleExtensionsCountVectorLaws
import WPFormalization.Probability.NNRealWindowBasis
/- Appendix F.4: genuine all-primitive tight spectrum convergence. The count
laws are proved locally for each finite family before applying the generic
classical continuity-semiring criterion in the genuine vague topology. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter WP.Probability
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}

/- The prefix presentation and original Moduli presentation use the same
full primitive tight process and the original normalization alpha(n/g). -/
theorem tight_spectrum_poisson_law_of_genus_tendsto
    (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A) (D : BuddLionsTightGeometry G T H Q A)
    (BM : ∀g n,(hg : 2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (QL : ProbabilityMeasure (PointMeasure ℝ≥0))
    (hPPP : IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QL) :
    LawConverges (fun j=>wpProbability G (gs j) (ns j))
      (fun j=>actualScaledTightPointMeasure Q (gs j) (ns j)) QL (fun ξ=>ξ) := by
  have hΞ : ∀ᶠj in atTop,AEMeasurable (scaledTightPointMeasure Q (gs j) (ns j))
      (TightConnected.connectedCuspProbability G (gs j) (ns j)) := by
    filter_upwards [hgs.eventually_ge_atTop 2] with j hj
    exact aemeasurable_tightLengthPointMeasure Q (BM _ _ hj) _ _
      (TightConnected.tightScale_pos _ (by positivity))
  apply lawConverges_actualScaledTightPointMeasure_of_prefix Q gs ns QL
  apply WP.External.pointMeasure_vague_of_semiring_count_laws ℝ≥0
    (fun j=>TightConnected.connectedCuspProbability G (gs j) (ns j))
    (fun j=>scaledTightPointMeasure Q (gs j) (ns j))
    (connected_cusp_probability_eventually_probability gs ns hgs) hΞ
    nonseparatingLengthIntensity nnrealRationalWindows
    (nnrealRationalWindows_basis nonseparatingLengthIntensity) QL hPPP
  intro d W _ hd
  obtain ⟨B,hB,hW⟩:=finite_windows_common_positive_bound W
  exact actual_tight_window_count_law T BZ Q A MI D BM gs ns hgs W hd B hB hW

theorem tight_spectrum_poisson_limit
    (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A) (D : BuddLionsTightGeometry G T H Q A)
    (BM : ∀g n,(hg : 2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (n : ℕ→ℕ) :
    ∃QL : ProbabilityMeasure (PointMeasure ℝ≥0),
      IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QL ∧
      LawConverges (fun g=>wpProbability G g (n g))
        (fun g=>actualScaledTightPointMeasure Q g (n g)) QL (fun ξ=>ξ) := by
  obtain ⟨QL,hPPP⟩:=WP.External.poisson_point_process_exists ℝ≥0 nonseparatingLengthIntensity
  exact ⟨QL,hPPP,tight_spectrum_poisson_law_of_genus_tendsto T BZ Q A MI D BM
    (fun g=>g) n tendsto_id QL hPPP⟩

end WP.Tight
