import WPFormalization.Tight.SpectrumTupleExtensionsSmallCoordinateSplit
import WPFormalization.Tight.SpectrumTupleExtensionsMarkedBadMoments
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

lemma scaled_good_set_count_measurable (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (g r n : ℕ) (hg : 2≤g) (I : Fin r→Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (B : ℝ) (hIB : ∀i,I i⊆Icc (0:ℝ) B) :
    Measurable (fun X : TightSurface G g 0 n (fun _=>0) (fun _=>0)=>
      (scaledGoodSetCount Q g r n I X : ℝ≥0∞)) := by
  classical
  let α:=tightScale ((n:ℝ)/g)
  have hα : 0<α := TightConnected.tightScale_pos _ (by positivity)
  let W : Fin r→Set ℝ := fun i=>(fun l=>α*l) ⁻¹' I i
  have hV : MeasurableSet ({x | ∀i : Fin r,x i∈W i} : Set (Fin r→ℝ)) :=
    RandomGeometry.pants_numeric_window_set_measurable r W
      (fun i=>(measurable_const.mul measurable_id) (hI i))
  have hm : Measurable (fun X : TightSurface G g 0 n (fun _=>0) (fun _=>0)=>
      ∑o : A.Orbit g 0 r,A.orbitSum o ({x |∀i,x i∈W i}.indicator (fun _=>1)) X) := by
    apply Finset.measurable_sum
    intro o ho
    exact MI.orbitSum_measurable o _ _ _ (measurable_const.indicator hV)
  convert hm using 1
  funext X
  exact (good_set_count_eq_orbit_sum Q X A W (B/α)
    (fun i l hl=>(le_div_iff₀ hα).mpr (by simpa only [mul_comm] using (hIB i hl).2))
    (by unfold Stable;omega))

lemma small_coordinate_count_eq_scaled_count {g n r : ℕ}
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (a B : ℝ) (i : Fin r) :
    Nat.card {Γ : Fin r→Curve Q X //GoodSetTuple Q X
      (smallCoordinateWindows r (a/tightScale ((n:ℝ)/g)) (B/tightScale ((n:ℝ)/g)) i) Γ} =
      scaledGoodSetCount Q g r n (smallCoordinateWindows r a B i) X := by
  have hI : smallCoordinateWindows r a B i=(fun j=>Icc (0:ℝ) (if j=i then a else B)) := by
    funext j
    by_cases hji : j=i <;> simp only [smallCoordinateWindows,hji,ite_true,ite_false]
  rw [hI,scaled_closed_box_count_eq_window_count]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro Γ
  simp only [GoodSetTuple,WindowTuple,zero_div]
  apply and_congr_right
  intro hgood
  apply forall_congr'
  intro j
  by_cases hji : j=i <;> simp only [smallCoordinateWindows,hji,ite_true,ite_false,Set.mem_Icc]

lemma small_coordinate_expectation_tendsto (T : TightRegions G)
    (BZ : BuddZonneveldTransform G T) (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (r : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (a B : ℝ) (haB : a≤B) (hB : 0≤B) :
    Tendsto (fun j=>∑i : Fin r,∫⁻X,
      (Nat.card {Γ : Fin r→Curve Q X //GoodSetTuple Q X
        (smallCoordinateWindows r (a/tightScale ((ns j:ℝ)/(gs j)))
          (B/tightScale ((ns j:ℝ)/(gs j))) i) Γ} : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop
      (𝓝 ((r:ℝ≥0∞)*(tightIntensity (Icc (0:ℝ) a)*tightIntensity (Icc (0:ℝ) B)^(r-1)))) := by
  have ht (i : Fin r) := scaled_good_set_count_expectation_tendsto T BZ Q A MI r gs ns hgs
    (smallCoordinateWindows r a B i)
    (fun j=>by by_cases hji : j=i <;> simp only [smallCoordinateWindows,hji,ite_true,ite_false] <;>
      exact measurableSet_Icc) B hB
    (fun j=>by by_cases hji : j=i
               · simp only [smallCoordinateWindows,hji,ite_true]
                 exact Icc_subset_Icc le_rfl haB
               · simp only [smallCoordinateWindows,hji,ite_false]
                 exact Subset.rfl)
  simp_rw [small_coordinate_intensity_product] at ht
  have hs:=tendsto_finsetSum Finset.univ (fun (i : Fin r) _=>ht i)
  simpa only [small_coordinate_count_eq_scaled_count,Finset.sum_const,nsmul_eq_mul,
    Finset.card_univ,Fintype.card_fin] using hs

lemma scaled_marked_zero_lower_integral_le (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (g r n : ℕ) (hg : 2≤g) (a B : ℝ) (haB : a≤B) :
    (∫⁻X,(scaledMarkedBadCount Q g r n 0 B X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G g n) ≤
      (∫⁻X,(scaledMarkedBadCount Q g r n a B X : ℝ≥0∞)
        ∂TightConnected.connectedCuspProbability G g n) +
      ∑i : Fin r,∫⁻X,
        (Nat.card {Γ : Fin r→Curve Q X //GoodSetTuple Q X
          (smallCoordinateWindows r (a/tightScale ((n:ℝ)/g)) (B/tightScale ((n:ℝ)/g)) i) Γ} : ℝ≥0∞)
        ∂TightConnected.connectedCuspProbability G g n := by
  have hα : 0<tightScale ((n:ℝ)/g) := TightConnected.tightScale_pos _ (by positivity)
  have hm (i : Fin r) : Measurable (fun X : TightSurface G g 0 n (fun _=>0) (fun _=>0)=>
      (Nat.card {Γ : Fin r→Curve Q X //GoodSetTuple Q X
        (smallCoordinateWindows r (a/tightScale ((n:ℝ)/g)) (B/tightScale ((n:ℝ)/g)) i) Γ} : ℝ≥0∞)) := by
    have hx:=scaled_good_set_count_measurable Q A MI g r n hg (smallCoordinateWindows r a B i)
      (fun j=>by by_cases hji : j=i <;> simp only [smallCoordinateWindows,hji,ite_true,ite_false] <;>
        exact measurableSet_Icc) B
      (fun j=>by by_cases hji : j=i
                 · simp only [smallCoordinateWindows,hji,ite_true]
                   exact Icc_subset_Icc le_rfl haB
                 · simp only [smallCoordinateWindows,hji,ite_false]
                   exact Subset.rfl)
    convert hx using 1
    funext X
    exact congrArg (fun q : ℕ=>(q:ℝ≥0∞)) (small_coordinate_count_eq_scaled_count X a B i)
  rw [←lintegral_finsetSum _ (fun i _=>hm i),←lintegral_add_right _
    (Finset.measurable_sum _ (fun i _=>hm i))]
  apply lintegral_mono
  intro X
  dsimp only
  have hh:=bad_good_set_count_le_positive_bad_add_small_coordinates Q X
    (fun _ : Fin r=>Icc (0:ℝ) (B/tightScale ((n:ℝ)/g)))
    (a/tightScale ((n:ℝ)/g)) (B/tightScale ((n:ℝ)/g))
    ((div_le_div_iff_of_pos_right hα).mpr haB) (fun _=>Subset.rfl) (B/tightScale ((n:ℝ)/g))
  have hnat : scaledMarkedBadCount Q g r n 0 B X ≤
      scaledMarkedBadCount Q g r n a B X +
      ∑i : Fin r,Nat.card {Γ : Fin r→Curve Q X // GoodSetTuple Q X
        (smallCoordinateWindows r (a/tightScale ((n:ℝ)/g)) (B/tightScale ((n:ℝ)/g)) i) Γ} := by
    simpa only [scaledMarkedBadCount,zero_div,GoodSetTuple,WindowTuple,Set.mem_Icc] using hh
  exact_mod_cast hnat

theorem scaled_marked_zero_lower_expectation_tendsto_zero (T : TightRegions G)
    (BZ : BuddZonneveldTransform G T) (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (D : BuddLionsTightGeometry G T H Q A)
    (r : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop) (B : ℝ) (hB : 0<B) :
    Tendsto (fun j=>∫⁻X,(scaledMarkedBadCount Q (gs j) r (ns j) 0 B X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop (𝓝 0) := by
  letI : IsLocallyFiniteMeasure tightIntensity :=
    IsLocallyFiniteMeasure.withDensity_ofReal TightConnected.tightIntensityDensity_continuous
  have hK : (r:ℝ≥0∞)*tightIntensity (Icc (0:ℝ) B)^(r-1)≠∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top r) (ENNReal.pow_ne_top isCompact_Icc.measure_lt_top.ne)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ζ hζ
  by_cases hζtop : ζ=∞
  · simp only [hζtop,le_top,eventually_const]
  have hζp : 0<ζ.toReal := ENNReal.toReal_pos hζ.ne' hζtop
  obtain ⟨a,ha,haB,hsmall⟩:=tight_intensity_small_window_mul_below B hB
    ((r:ℝ≥0∞)*tightIntensity (Icc (0:ℝ) B)^(r-1)) hK
    (ENNReal.ofReal (ζ.toReal/2)) (ENNReal.ofReal_pos.mpr (half_pos hζp))
  have hsmall' : (r:ℝ≥0∞)*(tightIntensity (Icc (0:ℝ) a)*tightIntensity (Icc (0:ℝ) B)^(r-1)) <
      ENNReal.ofReal (ζ.toReal/2) := by
    convert hsmall using 1 <;> ac_rfl
  have hpos := scaled_marked_bad_count_expectation_tendsto_zero T BZ Q A MI D r gs ns hgs a B ha haB.le
  have hshort := small_coordinate_expectation_tendsto T BZ Q A MI r gs ns hgs a B haB.le hB.le
  filter_upwards [hgs.eventually_ge_atTop 2,
    hpos.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hζp))),
    hshort.eventually (gt_mem_nhds hsmall')] with j hj hp hs
  have hb := scaled_marked_zero_lower_integral_le Q A MI (gs j) r (ns j) hj a B haB.le
  apply hb.trans ((add_le_add hp.le hs.le).trans_eq ?_)
  rw [←ENNReal.ofReal_add (half_pos hζp).le (half_pos hζp).le]
  have heq : ζ.toReal/2+ζ.toReal/2=ζ.toReal := by ring
  rw [heq,ENNReal.ofReal_toReal hζtop]

lemma marked_scaled_good_count_integral_le_closed_box
    (Q : TightGeodesicGeometry G T H) (g r n : ℕ) (I : Fin r→Set ℝ)
    (B : ℝ) (hIB : ∀i,I i⊆Icc (0:ℝ) B) :
    (∫⁻X,((if BadConfiguration Q X (B/tightScale ((n:ℝ)/g)) then
      scaledGoodSetCount Q g r n I X else 0 : ℕ) : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G g n) ≤
    ∫⁻X,(scaledMarkedBadCount Q g r n 0 B X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G g n := by
  have hα : 0<tightScale ((n:ℝ)/g) := TightConnected.tightScale_pos _ (by positivity)
  apply lintegral_mono
  intro X
  dsimp only
  have hc := good_set_count_le_closed_box Q X
    (fun i=>(fun l=>tightScale ((n:ℝ)/g)*l) ⁻¹' I i) 0 (B/tightScale ((n:ℝ)/g)) (by
      intro i l hl
      have hh:=hIB i hl
      exact ⟨(by nlinarith [hh.1] : 0≤l),
        (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using hh.2)⟩)
  by_cases hb : BadConfiguration Q X (B/tightScale ((n:ℝ)/g))
  · simp only [hb,ite_true,scaledMarkedBadCount,zero_div]
    exact_mod_cast hc
  · simp only [hb,ite_false,scaledMarkedBadCount,zero_div,le_refl]

theorem marked_scaled_good_count_expectation_tendsto_zero (T : TightRegions G)
    (BZ : BuddZonneveldTransform G T) (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (D : BuddLionsTightGeometry G T H Q A)
    (r : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (I : Fin r→Set ℝ) (B : ℝ) (hB : 0<B) (hIB : ∀i,I i⊆Icc (0:ℝ) B) :
    Tendsto (fun j=>∫⁻X,((if BadConfiguration Q X (B/tightScale ((ns j:ℝ)/(gs j))) then
      scaledGoodSetCount Q (gs j) r (ns j) I X else 0 : ℕ) : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop (𝓝 0) := by
  have ht:=scaled_marked_zero_lower_expectation_tendsto_zero T BZ Q A MI D r gs ns hgs B hB
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ζ hζ
  filter_upwards [ENNReal.tendsto_nhds_zero.mp ht ζ hζ] with j hj
  exact (marked_scaled_good_count_integral_le_closed_box Q (gs j) r (ns j) I B hIB).trans hj

end WP.Tight
