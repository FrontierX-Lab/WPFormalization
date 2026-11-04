import WPFormalization.Tight.SpectrumTupleExtensionsShortAugmentedMoments
import WPFormalization.Tight.SpectrumTupleExtensionsBadBounds
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

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

lemma marked_bad_no_simple_length_ties_ae
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (D : BuddLionsTightGeometry G T H Q A) (g n : ℕ) (hg : 2≤g) :
    ∀ᵐ X ∂TightConnected.connectedCuspProbability G g n,Q.NoSimpleLengthTies (X:=X) := by
  exact Measure.ae_smul_measure (D.no_ties_ae g n hg) _


lemma separating_shifted_finite_sum_expectation_tendsto_zero (T : TightRegions G)
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (BZ : BuddZonneveldTransform G T) (MI : BuddLionsTightIntegration G T H Q A)
    (r M : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop) (B : ℝ) (hB : 0≤B) :
    Tendsto (fun j=>∑m : Fin M,∫⁻X,
      (TightSeparating.tightSeparatingCount Q A (r+m.val)
        (B/tightScale ((ns j:ℝ)/(gs j))) X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
    (fun (m : Fin M) _=>separating_expectation_tendsto_zero T Q A BZ MI (r+m.val) gs ns hgs B hB)

lemma tight_intensity_small_window_mul_below (a : ℝ) (ha : 0<a)
    (K : ℝ≥0∞) (hK : K≠∞) (ζ : ℝ≥0∞) (hζ : 0<ζ) :
    ∃ ε : ℝ, 0<ε ∧ ε<a ∧ tightIntensity (Icc (0:ℝ) ε)*K<ζ := by
  let : IsLocallyFiniteMeasure tightIntensity :=
    IsLocallyFiniteMeasure.withDensity_ofReal TightConnected.tightIntensityDensity_continuous
  let : NullSingletonClass tightIntensity := by unfold tightIntensity;infer_instance
  have ht : Tendsto (fun ε : ℝ=>tightIntensity (Icc (-ε) ε)) (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa only [zero_sub,zero_add] using tendsto_measure_Icc tightIntensity (0:ℝ)
  have htm : Tendsto (fun ε : ℝ=>tightIntensity (Icc (-ε) ε)*K) (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const ht (Or.inr hK)
  have hh : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),tightIntensity (Icc (-ε) ε)*K<ζ :=
    (htm.eventually (gt_mem_nhds hζ)).filter_mono nhdsWithin_le_nhds
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),0<ε := self_mem_nhdsWithin
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),ε<a :=
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε,hε,hea,hm⟩ := (hp.and (hb.and hh)).exists
  refine ⟨ε,hε,hea,lt_of_le_of_lt ?_ hm⟩
  exact mul_le_mul_left (measure_mono (Icc_subset_Icc (by linarith) le_rfl)) K

def scaledMarkedBadCount (Q : TightGeodesicGeometry G T H)
    (g r n : ℕ) (a B : ℝ)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) : ℕ :=
  if BadConfiguration Q X (B/tightScale ((n:ℝ)/g)) then
    Nat.card {Γ : Fin r→Curve Q X // WindowTuple Q X
      (fun _=>a/tightScale ((n:ℝ)/g)) (fun _=>B/tightScale ((n:ℝ)/g)) Γ} else 0

lemma scaled_marked_bad_integral_le_short_add_separating
    (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (D : BuddLionsTightGeometry G T H Q A) (MI : BuddLionsTightIntegration G T H Q A)
    {g n r : ℕ} (hg : 2≤g) (ε a B : ℝ) (he : 0<ε) (hea : ε<a) (haB : a≤B)
    (hgenus : 2*B*((r:ℝ)+2)/ε+2<g) :
    (∫⁻X,(scaledMarkedBadCount Q g r n a B X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G g n) ≤
      (∫⁻X,(scaledShortAugmentedCount Q g r n (fun _=>a) (fun _=>B) ε X : ℝ≥0∞)
        ∂TightConnected.connectedCuspProbability G g n) +
      (∑m : Fin 4,∫⁻X,(TightSeparating.tightSeparatingCount Q A (r+m.val)
        ((2*B+ε)/tightScale ((n:ℝ)/g)) X : ℝ≥0∞)
        ∂TightConnected.connectedCuspProbability G g n) +
      ∑m : Fin (⌈2*B*((r:ℝ)+2)/ε⌉₊+1),∫⁻X,
        (TightSeparating.tightSeparatingCount Q A (r+m.val)
          ((B*((r:ℝ)+2))/tightScale ((n:ℝ)/g)) X : ℝ≥0∞)
        ∂TightConnected.connectedCuspProbability G g n := by
  classical
  let μ := TightConnected.connectedCuspProbability G g n
  let S : TightSurface G g 0 n (fun _=>0) (fun _=>0)→ℝ≥0∞ := fun X=>
    scaledShortAugmentedCount Q g r n (fun _=>a) (fun _=>B) ε X
  let F (m : Fin 4) : TightSurface G g 0 n (fun _=>0) (fun _=>0)→ℝ≥0∞ := fun X=>
    TightSeparating.tightSeparatingCount Q A (r+m.val) ((2*B+ε)/tightScale ((n:ℝ)/g)) X
  let M := ⌈2*B*((r:ℝ)+2)/ε⌉₊+1
  let K (m : Fin M) : TightSurface G g 0 n (fun _=>0) (fun _=>0)→ℝ≥0∞ := fun X=>
    TightSeparating.tightSeparatingCount Q A (r+m.val) ((B*((r:ℝ)+2))/tightScale ((n:ℝ)/g)) X
  have hmF (m : Fin 4) : Measurable (F m) := by
    simpa only [F,ENNReal.ofReal_natCast] using
      (TightSeparating.tightSeparatingCount_measurable A MI g (r+m.val) n
        (by unfold Stable;omega) _).ennreal_ofReal
  have hmK (m : Fin M) : Measurable (K m) := by
    simpa only [K,ENNReal.ofReal_natCast] using
      (TightSeparating.tightSeparatingCount_measurable A MI g (r+m.val) n
        (by unfold Stable;omega) _).ennreal_ofReal
  change (∫⁻X,(scaledMarkedBadCount Q g r n a B X : ℝ≥0∞) ∂μ) ≤
    (∫⁻X,S X ∂μ)+(∑m : Fin 4,∫⁻X,F m X ∂μ)+∑m : Fin M,∫⁻X,K m X ∂μ
  calc
    _ ≤ ∫⁻X,(S X+∑m : Fin 4,F m X)+(∑m : Fin M,K m X) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [marked_bad_no_simple_length_ties_ae A D g n hg] with X hX
      have hα : 0<tightScale ((n:ℝ)/g) := TightConnected.tightScale_pos _ (by positivity)
      have hb := window_bad_indicator_le_short_add_separating Q A X D
        (fun _=>a/tightScale ((n:ℝ)/g)) (fun _=>B/tightScale ((n:ℝ)/g))
        (tightScale ((n:ℝ)/g))⁻¹ ε a B hg (inv_pos.mpr hα) he hea haB hgenus hX
        (fun _=>by ring_nf;exact le_rfl) (fun _=>by ring_nf;exact le_rfl)
      have h1 : (tightScale ((n:ℝ)/g))⁻¹*B=B/tightScale ((n:ℝ)/g) := by ring
      have h2 : (tightScale ((n:ℝ)/g))⁻¹*ε=ε/tightScale ((n:ℝ)/g) := by ring
      have h3 : (tightScale ((n:ℝ)/g))⁻¹*(2*B+ε)=(2*B+ε)/tightScale ((n:ℝ)/g) := by ring
      have h4 : B/tightScale ((n:ℝ)/g)*((r:ℝ)+2)=(B*((r:ℝ)+2))/tightScale ((n:ℝ)/g) := by ring
      rw [h1,h2,h3,h4] at hb
      dsimp only [scaledMarkedBadCount,S,F,K,M,scaledShortAugmentedCount,
        TightSeparating.tightSeparatingCount]
      exact_mod_cast hb
    _ = _ := by
      rw [lintegral_add_right _ (Finset.measurable_sum _ (fun m _=>hmK m)),
        lintegral_add_right _ (Finset.measurable_sum _ (fun m _=>hmF m)),
        lintegral_finsetSum _ (fun m _=>hmF m),
        lintegral_finsetSum _ (fun m _=>hmK m)]


theorem scaled_marked_bad_count_expectation_tendsto_zero (T : TightRegions G)
    (BZ : BuddZonneveldTransform G T) (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (D : BuddLionsTightGeometry G T H Q A)
    (r : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (a B : ℝ) (ha : 0<a) (haB : a≤B) :
    Tendsto (fun j=>∫⁻X,(scaledMarkedBadCount Q (gs j) r (ns j) a B X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure tightIntensity :=
    IsLocallyFiniteMeasure.withDensity_ofReal TightConnected.tightIntensityDensity_continuous
  have hK : tightIntensity (Icc a B)^r≠∞ :=
    ENNReal.pow_ne_top isCompact_Icc.measure_lt_top.ne
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ζ hζ
  by_cases hζtop : ζ=∞
  · simp only [hζtop,le_top,eventually_const]
  have hζp : 0<ζ.toReal := ENNReal.toReal_pos hζ.ne' hζtop
  have hthird : 0<ζ.toReal/3 := by positivity
  obtain ⟨ε,he,hea,hsmall⟩ := tight_intensity_small_window_mul_below a ha
    (tightIntensity (Icc a B)^r) hK (ENNReal.ofReal (ζ.toReal/3))
      (ENNReal.ofReal_pos.mpr hthird)
  have htshort := scaled_short_augmented_const_expectation_tendsto T BZ Q A MI r gs ns hgs
    a B ε ha.le (ha.trans_le haB).le
  have htsep1 := separating_shifted_finite_sum_expectation_tendsto_zero T Q A BZ MI r 4 gs ns hgs
    (2*B+ε) (by have := ha.trans_le haB;positivity)
  have htsep2 := separating_shifted_finite_sum_expectation_tendsto_zero T Q A BZ MI r
    (⌈2*B*((r:ℝ)+2)/ε⌉₊+1) gs ns hgs (B*((r:ℝ)+2))
    (by have := ha.trans_le haB;positivity)
  have hgen : ∀ᶠj in atTop,2*B*((r:ℝ)+2)/ε+2<(gs j:ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hgs).eventually_gt_atTop _
  filter_upwards [hgs.eventually_ge_atTop 2,hgen,
    htshort.eventually (gt_mem_nhds hsmall),
    htsep1.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hthird)),
    htsep2.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hthird))]
    with j hj hg hjshort hjsep1 hjsep2
  have hb := scaled_marked_bad_integral_le_short_add_separating Q A D MI
    (g:=gs j) (n:=ns j) (r:=r) hj ε a B he hea haB hg
  apply hb.trans ((add_le_add (add_le_add hjshort.le hjsep1.le) hjsep2.le).trans_eq ?_)
  rw [←ENNReal.ofReal_add hthird.le hthird.le,
    ←ENNReal.ofReal_add (by positivity) hthird.le]
  have heq : (ζ.toReal/3+ζ.toReal/3)+ζ.toReal/3=ζ.toReal := by ring
  rw [heq,ENNReal.ofReal_toReal hζtop]

end WP.Tight
