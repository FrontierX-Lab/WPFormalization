import WPFormalization.Tight.SpectrumTupleExtensionsSetWindows
import WPFormalization.Tight.ConnectedOrbitMoments
import WPFormalization.Tight.SeparatingActualExpectation
/- Appendix F.4 actual full good-tuple expectation limits from the locally
proved connected/separating split and F.2/F.3. No moment input is assumed. -/
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter SpectrumTupleExtensions
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Q : TightGeodesicGeometry G T H}

def scaledGoodSetCount (Q : TightGeodesicGeometry G T H) (g r n : ℕ)
    (I : Fin r→Set ℝ) (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) : ℕ :=
  Nat.card {Γ : Fin r→Curve Q X //
    GoodSetTuple Q X (fun i=>(fun l=>tightScale ((n:ℝ)/g)*l) ⁻¹' I i) Γ}

lemma prefixProbability_eq_connectedProbability (g n : ℕ) (hs : Stable g n) :
    TightSeparating.tightPrefixWpProbability G g n =
      TightConnected.connectedCuspProbability G g n := by
  have hm : ENNReal.ofReal (cuspVolume G g n) = G.wpMeasure g n (fun _=>0) univ := by
    unfold cuspVolume wpVolume
    exact ENNReal.ofReal_toReal (G.finite_volume g n _ hs (fun _=>le_rfl))
  unfold TightSeparating.tightPrefixWpProbability TightConnected.connectedCuspProbability
  rw [hm]

lemma separating_expectation_tendsto_zero (T : TightRegions G)
    (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (BZ : BuddZonneveldTransform G T) (MI : BuddLionsTightIntegration G T H Q A)
    (r : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (B : ℝ) (hB : 0≤B) :
    Tendsto (fun j=>∫⁻ X,
      (TightSeparating.tightSeparatingCount Q A r (B/tightScale ((ns j:ℝ)/(gs j))) X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases he : ε=∞
  · simp only [he,le_top,eventually_const]
  have hep : 0<ε.toReal := ENNReal.toReal_pos hε.ne' he
  obtain ⟨N,hN⟩:=TightSeparating.tight_separating_expectation_uniform T A BZ MI r B hB ε.toReal hep
  filter_upwards [hgs.eventually_ge_atTop (max N 2)] with j hj
  rw [←prefixProbability_eq_connectedProbability (gs j) (ns j) (by unfold Stable;omega)]
  exact (hN (gs j) (by omega) (ns j)).trans_eq (ENNReal.ofReal_toReal he)

lemma scaled_good_set_count_expectation_tendsto (T : TightRegions G)
    (BZ : BuddZonneveldTransform G T) (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (r : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (I : Fin r→Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (B : ℝ) (hB : 0≤B) (hIB : ∀i,I i⊆Icc (0:ℝ) B) :
    Tendsto (fun j=>∫⁻ X,(scaledGoodSetCount Q (gs j) r (ns j) I X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop
      (𝓝 (∏i,tightIntensity (I i))) := by
  let C : ℕ→ℝ≥0∞ := fun j=>∫⁻X,
    (TightConnected.connectedScaledWindowCount Q A (gs j) r (ns j) I X : ℝ≥0∞)
    ∂TightConnected.connectedCuspProbability G (gs j) (ns j)
  let S : ℕ→ℝ≥0∞ := fun j=>∫⁻X,
    (TightSeparating.tightSeparatingCount Q A r (B/tightScale ((ns j:ℝ)/(gs j))) X : ℝ≥0∞)
    ∂TightConnected.connectedCuspProbability G (gs j) (ns j)
  have hc : Tendsto C atTop (𝓝 (∏i,tightIntensity (I i))) :=
    TightConnected.connected_scaled_window_count_expectation_tendsto_intensity T BZ Q A MI r gs ns hgs I hI B hB hIB
  have hs : Tendsto S atTop (𝓝 0) := separating_expectation_tendsto_zero T Q A BZ MI r gs ns hgs B hB
  have hbounds : ∀ᶠj in atTop,
      C j ≤ (∫⁻X,(scaledGoodSetCount Q (gs j) r (ns j) I X : ℝ≥0∞)
        ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) ∧
      (∫⁻X,(scaledGoodSetCount Q (gs j) r (ns j) I X : ℝ≥0∞)
        ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) ≤ C j+S j := by
    filter_upwards [hgs.eventually_ge_atTop 2] with j hj
    have hα : 0<tightScale ((ns j:ℝ)/(gs j)) := TightConnected.tightScale_pos _ (by positivity)
    let W : Fin r→Set ℝ := fun i=>(fun l=>tightScale ((ns j:ℝ)/(gs j))*l) ⁻¹' I i
    have hw : ∀i,∀l∈W i,l≤B/tightScale ((ns j:ℝ)/(gs j)) := by
      intro i l hl
      apply (le_div_iff₀ hα).mpr
      simpa only [mul_comm] using (hIB i hl).2
    have hst : Stable (gs j) 0 := by unfold Stable;omega
    have he (X : TightSurface G (gs j) 0 (ns j) (fun _=>0) (fun _=>0)) :
        (TightConnected.connectedScaledWindowCount Q A (gs j) r (ns j) I X : ℝ≥0∞) =
        ∑o∈Finset.univ.filter (fun o : A.Orbit (gs j) 0 r=>(A.cut o).components=1),
          A.orbitSum o ({x | ∀i,x i∈W i}.indicator (fun _=>1)) X := by
      exact TightConnected.connected_scaled_window_count_eq_orbit_sum Q A (gs j) r (ns j) hj I B hIB X
    refine ⟨?_,?_⟩
    · apply lintegral_mono
      intro X
      dsimp only
      rw [he X]
      exact connected_count_le_good_set_count Q X A W _ hw hst
    · dsimp only [C,S]
      have hm : Measurable (fun X=>(TightConnected.connectedScaledWindowCount Q A (gs j) r (ns j) I X : ℝ≥0∞)) :=
        TightConnected.connected_scaled_window_count_measurable Q A MI (gs j) r (ns j) hj I hI B hIB
      rw [←lintegral_add_left hm]
      apply lintegral_mono
      intro X
      dsimp only
      rw [he X]
      exact good_set_count_le_connected_add_separating Q X A W _ hw hst
  have hupper := hc.add hs
  simp only [add_zero] at hupper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hc hupper
    (hbounds.mono fun _ h=>h.1) (hbounds.mono fun _ h=>h.2)

lemma scaled_closed_box_count_eq_window_count
    (Q : TightGeodesicGeometry G T H) {g r n : ℕ}
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0))
    (lo hi : Fin r→ℝ) :
    scaledGoodSetCount Q g r n (fun i=>Icc (lo i) (hi i)) X =
      Nat.card {Γ : Fin r→Curve Q X // WindowTuple Q X
        (fun i=>lo i/tightScale ((n:ℝ)/g)) (fun i=>hi i/tightScale ((n:ℝ)/g)) Γ} := by
  have hα : 0<tightScale ((n:ℝ)/g) := TightConnected.tightScale_pos _ (by positivity)
  unfold scaledGoodSetCount
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro Γ
  simp only [GoodSetTuple,WindowTuple,Set.mem_preimage,Set.mem_Icc,
    div_le_iff₀ hα,le_div_iff₀ hα,mul_comm]

end WP.Tight
