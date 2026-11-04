import WPFormalization.Tight.SpectrumTupleExtensionsGoodMoments
import WPFormalization.Tight.SpectrumTupleExtensionsBadBounds
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
/- Appendix F.4 local actual-spectrum proof. The original normalized WP
measure and the complete primitive tight catalogue are retained; all limits
are proved from the previously formalized geometric moment producers. -/
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter SpectrumTupleExtensions
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Q : TightGeodesicGeometry G T H}

lemma tight_intensity_small_window (η : ℝ≥0∞) (hη : 0<η) :
    ∃ ε : ℝ,0<ε ∧ tightIntensity (Icc (0:ℝ) ε)<η := by
  letI : IsLocallyFiniteMeasure tightIntensity :=
    IsLocallyFiniteMeasure.withDensity_ofReal TightConnected.tightIntensityDensity_continuous
  letI : NullSingletonClass tightIntensity := by unfold tightIntensity;infer_instance
  have ht : Tendsto (fun ε : ℝ=>tightIntensity (Icc (-ε) ε)) (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa only [zero_sub,zero_add] using
      tendsto_measure_Icc tightIntensity (0:ℝ)
  have hh : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),tightIntensity (Icc (-ε) ε)<η :=
    (ht.eventually (gt_mem_nhds hη)).filter_mono nhdsWithin_le_nhds
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),0<ε := self_mem_nhdsWithin
  obtain ⟨ε,hpos,hsmall⟩ := (hp.and hh).exists
  exact ⟨ε,hpos,(measure_mono (Icc_subset_Icc (by linarith) le_rfl)).trans_lt hsmall⟩

lemma no_simple_length_ties_ae_connected
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (D : BuddLionsTightGeometry G T H Q A) (g n : ℕ) (hg : 2≤g) :
    ∀ᵐ X ∂TightConnected.connectedCuspProbability G g n,Q.NoSimpleLengthTies (X:=X) := by
  exact Measure.ae_smul_measure (D.no_ties_ae g n hg) _

lemma separating_finite_sum_expectation_tendsto_zero (T : TightRegions G)
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (BZ : BuddZonneveldTransform G T) (MI : BuddLionsTightIntegration G T H Q A)
    (M : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop) (B : ℝ) (hB : 0≤B) :
    Tendsto (fun j=>∑m : Fin M,∫⁻X,
      (TightSeparating.tightSeparatingCount Q A (0+m.val)
        (B/tightScale ((ns j:ℝ)/(gs j))) X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ
    (fun (m : Fin M) _=>separating_expectation_tendsto_zero T Q A BZ MI (0+m.val) gs ns hgs B hB)

lemma bad_mass_le_short_add_separating
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (D : BuddLionsTightGeometry G T H Q A) (MI : BuddLionsTightIntegration G T H Q A)
    {g n : ℕ} (hg : 2≤g) (BM : TightGeodesicBorelModel G T H Q g n hg)
    (ε B : ℝ) (he : 0<ε) (hB : 0<B) (hgenus : 2*B*2/ε+2<g) :
    TightConnected.connectedCuspProbability G g n
      {X | BadConfiguration Q X (B/tightScale ((n:ℝ)/g))} ≤
      (∫⁻ X,(Nat.card {Γ : Fin 1→Curve Q X //
        WindowTuple Q X (fun _=>0) (fun _=>ε/tightScale ((n:ℝ)/g)) Γ} : ℝ≥0∞)
        ∂TightConnected.connectedCuspProbability G g n) +
      ∑m : Fin (⌈2*B*(((0:ℕ):ℝ)+2)/ε⌉₊+1),∫⁻X,
        (TightSeparating.tightSeparatingCount Q A (0+m.val)
          ((B*2)/tightScale ((n:ℝ)/g)) X : ℝ≥0∞)
        ∂TightConnected.connectedCuspProbability G g n := by
  have hα : 0<tightScale ((n:ℝ)/g) := TightConnected.tightScale_pos _ (by positivity)
  have hbad : MeasurableSet {X : TightSurface G g 0 n (fun _=>0) (fun _=>0) |
      BadConfiguration Q X (B/tightScale ((n:ℝ)/g))} :=
    measurableSet_actual_bad_configuration BM _
  have hm (m : Fin (⌈2*B*(((0:ℕ):ℝ)+2)/ε⌉₊+1)) : Measurable
      (fun X : TightSurface G g 0 n (fun _=>0) (fun _=>0)=>
        (TightSeparating.tightSeparatingCount Q A (0+m.val) ((B*2)/tightScale ((n:ℝ)/g)) X : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_natCast] using
      (TightSeparating.tightSeparatingCount_measurable A MI g (0+m.val) n
        (by unfold Stable;omega) ((B*2)/tightScale ((n:ℝ)/g))).ennreal_ofReal
  have heq : TightConnected.connectedCuspProbability G g n
      {X | BadConfiguration Q X (B/tightScale ((n:ℝ)/g))} =
      ∫⁻X,if BadConfiguration Q X (B/tightScale ((n:ℝ)/g)) then (1:ℝ≥0∞) else 0
        ∂TightConnected.connectedCuspProbability G g n := by
    symm
    simpa only [Set.indicator_apply,Set.mem_setOf_eq,one_mul] using lintegral_indicator_const
      (μ:=TightConnected.connectedCuspProbability G g n) hbad 1
  rw [heq,←lintegral_finsetSum _ (fun m _=>hm m),←lintegral_add_right _
    (Finset.measurable_sum _ (fun m _=>hm m))]
  apply lintegral_mono_ae
  filter_upwards [no_simple_length_ties_ae_connected A D g n hg] with X hx
  have hh := bad_indicator_le_short_window_add_separating Q X A D
    (tightScale ((n:ℝ)/g))⁻¹ ε B (inv_pos.mpr hα) he hB (by simpa using hgenus) hx
  simp only [Nat.cast_zero,zero_add] at hh
  have h2 : (tightScale ((n:ℝ)/g))⁻¹*B*2=(B*2)/tightScale ((n:ℝ)/g) := by ring
  have h1 : (tightScale ((n:ℝ)/g))⁻¹*B=B/tightScale ((n:ℝ)/g) := by ring
  have heqε : (tightScale ((n:ℝ)/g))⁻¹*ε=ε/tightScale ((n:ℝ)/g) := by ring
  rw [h2,h1,heqε] at hh
  simpa only [TightSeparating.tightSeparatingCount,Nat.zero_add] using hh

theorem bad_configuration_measure_tendsto_zero (T : TightRegions G)
    (BZ : BuddZonneveldTransform G T) (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (D : BuddLionsTightGeometry G T H Q A)
    (BM : ∀g n,(hg : 2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop) (B : ℝ) (hB : 0<B) :
    Tendsto (fun j=>TightConnected.connectedCuspProbability G (gs j) (ns j)
      {X | BadConfiguration Q X (B/tightScale ((ns j:ℝ)/(gs j)))}) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ζ hζ
  by_cases hζtop : ζ=∞
  · simp only [hζtop,le_top,eventually_const]
  have hζp : 0<ζ.toReal := ENNReal.toReal_pos hζ.ne' hζtop
  obtain ⟨ε,he,hsmall⟩ := tight_intensity_small_window
    (ENNReal.ofReal (ζ.toReal/2)) (ENNReal.ofReal_pos.mpr (half_pos hζp))
  have htshort : Tendsto (fun j=>∫⁻X,
      (Nat.card {Γ : Fin 1→Curve Q X // WindowTuple Q X (fun _=>0)
        (fun _=>ε/tightScale ((ns j:ℝ)/(gs j))) Γ} : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop
      (𝓝 (tightIntensity (Icc (0:ℝ) ε))) := by
    have ht := scaled_good_set_count_expectation_tendsto T BZ Q A MI 1 gs ns hgs
      (fun _=>Icc (0:ℝ) ε) (fun _=>measurableSet_Icc) ε he.le (fun _=>Subset.rfl)
    simpa only [scaled_closed_box_count_eq_window_count,zero_div,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin,pow_one] using ht
  have htsep := separating_finite_sum_expectation_tendsto_zero T Q A BZ MI
    (⌈2*B*(((0:ℕ):ℝ)+2)/ε⌉₊+1) gs ns hgs (B*2) (by positivity)
  have hgen : ∀ᶠj in atTop,2*B*2/ε+2<(gs j:ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hgs).eventually_gt_atTop _
  filter_upwards [hgs.eventually_ge_atTop 2,hgen,
    htshort.eventually (gt_mem_nhds hsmall),
    htsep.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hζp)))]
    with j hj hg hjshort hjsep
  have hb:=bad_mass_le_short_add_separating A D MI hj (BM (gs j) (ns j) hj) ε B he hB hg
  have hsum := add_le_add hjshort.le hjsep.le
  apply hb.trans (hsum.trans_eq ?_)
  rw [←ENNReal.ofReal_add (half_pos hζp).le (half_pos hζp).le]
  have heq : ζ.toReal/2+ζ.toReal/2=ζ.toReal := by ring
  rw [heq,ENNReal.ofReal_toReal hζtop]

end WP.Tight
