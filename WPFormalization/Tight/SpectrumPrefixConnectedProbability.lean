import WPFormalization.Tight.SpectrumPrefixConnected
import WPFormalization.Tight.SpectrumTupleExtensionsBadProbability
import WPFormalization.Tight.SpectrumTupleExtensionsZeroLowerMarkedMoments
import WPFormalization.Tight.SpectrumTupleExtensionsActualProcess
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter SpectrumTupleExtensions
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Q : TightGeodesicGeometry G T H} {g n : ℕ}

lemma full_prefix_failure_measure_le
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A)
    (g n : ℕ) (hg : 2≤g) (B : ℝ) (N : ℕ) :
    TightConnected.connectedCuspProbability G g n
      {X | ¬FullPrefixConnected Q A X (B/tightScale ((n:ℝ)/g))} ≤
      TightConnected.connectedCuspProbability G g n
        {X | BadConfiguration Q X (B/tightScale ((n:ℝ)/g))} +
      (∫⁻X,(scaledGoodSetCount Q g 1 n (fun _=>Icc (0:ℝ) B) X : ℝ≥0∞)
        ∂TightConnected.connectedCuspProbability G g n)/((N+1:ℕ):ℝ≥0∞) +
      ∑m : Fin N,∫⁻X,(TightSeparating.tightSeparatingCount Q A (1+m.val)
        (B/tightScale ((n:ℝ)/g)) X : ℝ≥0∞)
        ∂TightConnected.connectedCuspProbability G g n := by
  classical
  let μ:=TightConnected.connectedCuspProbability G g n
  let b:=B/tightScale ((n:ℝ)/g)
  let f : TightSurface G g 0 n (fun _=>0) (fun _=>0)→ℝ≥0∞ := fun X=>
    scaledGoodSetCount Q g 1 n (fun _=>Icc (0:ℝ) B) X
  let S (m : Fin N) : TightSurface G g 0 n (fun _=>0) (fun _=>0)→ℝ≥0∞ := fun X=>
    TightSeparating.tightSeparatingCount Q A (1+m.val) b X
  have hmf : Measurable f := scaled_good_set_count_measurable Q A MI g 1 n hg
    (fun _=>Icc (0:ℝ) B) (fun _=>measurableSet_Icc) B (fun _=>Subset.rfl)
  have hmS (m : Fin N) : Measurable (S m) := by
    simpa only [S,ENNReal.ofReal_natCast] using
      (TightSeparating.tightSeparatingCount_measurable A MI g (1+m.val) n
        (by unfold Stable;omega) b).ennreal_ofReal
  have hgood (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) :
      scaledGoodSetCount Q g 1 n (fun _=>Icc (0:ℝ) B) X =
        Nat.card {Γ : Fin 1→Curve Q X // WindowTuple Q X (fun _=>0) (fun _=>b) Γ} := by
    simpa only [zero_div] using scaled_closed_box_count_eq_window_count Q X
      (fun _ : Fin 1=>0) (fun _=>B)
  have htail : μ {X | N<Nat.card {Γ : Fin 1→Curve Q X // WindowTuple Q X (fun _=>0) (fun _=>b) Γ}} ≤
      (∫⁻X,f X ∂μ)/((N+1:ℕ):ℝ≥0∞) := by
    calc
      _ ≤ μ {X | ((N+1:ℕ):ℝ≥0∞)≤f X} := by
        apply measure_mono
        intro X hX
        change ((N+1:ℕ):ℝ≥0∞)≤(scaledGoodSetCount Q g 1 n (fun _=>Icc (0:ℝ) B) X : ℝ≥0∞)
        rw [hgood X]
        exact_mod_cast Nat.succ_le_iff.mpr hX
      _ ≤ _ := meas_ge_le_lintegral_div hmf.aemeasurable (by positivity) (by simp)
  have hsep : μ {X | 1≤∑m : Fin N,Nat.card {Γ : Fin (1+m.val)→Curve Q X //
      SeparatingTuple Q A X (1+m.val) b Γ}} ≤ ∑m : Fin N,∫⁻X,S m X ∂μ := by
    calc
      _ ≤ μ {X | (1:ℝ≥0∞)≤∑m : Fin N,S m X} := by
        apply measure_mono
        intro X hX
        dsimp only [Set.mem_setOf_eq,S,TightSeparating.tightSeparatingCount]
        exact_mod_cast hX
      _ ≤ (∫⁻X,∑m : Fin N,S m X ∂μ)/(1:ℝ≥0∞) :=
        meas_ge_le_lintegral_div (Finset.measurable_sum _ (fun m _=>hmS m)).aemeasurable
          one_ne_zero (by simp)
      _ = _ := by rw [div_one,lintegral_finsetSum _ (fun m _=>hmS m)]
  calc
    _ ≤ μ (({X | BadConfiguration Q X b} ∪
        {X | N<Nat.card {Γ : Fin 1→Curve Q X // WindowTuple Q X (fun _=>0) (fun _=>b) Γ}}) ∪
        {X | 1≤∑m : Fin N,Nat.card {Γ : Fin (1+m.val)→Curve Q X //
          SeparatingTuple Q A X (1+m.val) b Γ}}) :=
      measure_mono (full_prefix_failure_subset_bad_tail_separating A b hg N)
    _ ≤ (μ {X | BadConfiguration Q X b} +
        μ {X | N<Nat.card {Γ : Fin 1→Curve Q X // WindowTuple Q X (fun _=>0) (fun _=>b) Γ}}) +
        μ {X | 1≤∑m : Fin N,Nat.card {Γ : Fin (1+m.val)→Curve Q X //
          SeparatingTuple Q A X (1+m.val) b Γ}} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add le_rfl htail) hsep


lemma prefix_div_nat_succ_tendsto_zero (C : ℝ≥0∞) (hC : C≠∞) :
    Tendsto (fun N : ℕ=>C/((N+1:ℕ):ℝ≥0∞)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ=>N+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_inv_nat_nhds_zero.comp hs) (Or.inr hC)

/-- The entire primitive tight prefix has simple, pairwise disjoint curves
and connected filled complement with probability tending to one. The failure
probability is controlled without selecting a proper subfamily. -/
theorem full_prefix_connected_failure_measure_tendsto_zero (T : TightRegions G)
    (BZ : BuddZonneveldTransform G T) (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (D : BuddLionsTightGeometry G T H Q A)
    (BM : ∀g n,(hg : 2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop) (B : ℝ) (hB : 0≤B) :
    Tendsto (fun j=>TightConnected.connectedCuspProbability G (gs j) (ns j)
      {X | ¬FullPrefixConnected Q A X (B/tightScale ((ns j:ℝ)/(gs j)))}) atTop (𝓝 0) := by
  by_cases hB0 : B=0
  · apply tendsto_const_nhds.congr'
    filter_upwards [hgs.eventually_ge_atTop 2] with j hj
    have he : {X : TightSurface G (gs j) 0 (ns j) (fun _=>0) (fun _=>0) |
        ¬FullPrefixConnected Q A X (B/tightScale ((ns j:ℝ)/(gs j)))}=∅ := by
      ext X
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      exact not_not.mpr (full_prefix_connected_of_nonpos A X _ hj (by simp only [hB0,zero_div,le_refl]))
    simp only [he,measure_empty]
  have hBpos : 0<B := lt_of_le_of_ne hB (Ne.symm hB0)
  let : IsLocallyFiniteMeasure tightIntensity :=
    IsLocallyFiniteMeasure.withDensity_ofReal TightConnected.tightIntensityDensity_continuous
  let K:=tightIntensity (Icc (0:ℝ) B)
  have hK : K≠∞ := isCompact_Icc.measure_lt_top.ne
  have hK1 : K+1≠∞ := ENNReal.add_ne_top.mpr ⟨hK,by simp⟩
  have hgood : Tendsto (fun j=>∫⁻X,
      (scaledGoodSetCount Q (gs j) 1 (ns j) (fun _=>Icc (0:ℝ) B) X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop (𝓝 K) := by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,pow_one] using
      scaled_good_set_count_expectation_tendsto T BZ Q A MI 1 gs ns hgs
        (fun _=>Icc (0:ℝ) B) (fun _=>measurableSet_Icc) B hB (fun _=>Subset.rfl)
  have hbad:=bad_configuration_measure_tendsto_zero T BZ Q A MI D BM gs ns hgs B hBpos
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ζ hζ
  by_cases hζtop : ζ=∞
  · simp only [hζtop,le_top,eventually_const]
  have hζp : 0<ζ.toReal := ENNReal.toReal_pos hζ.ne' hζtop
  have hthird : 0<ζ.toReal/3 := by positivity
  obtain ⟨N,hN⟩:=((prefix_div_nat_succ_tendsto_zero (K+1) hK1).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr hthird))).exists
  have hsep:=separating_shifted_finite_sum_expectation_tendsto_zero T Q A BZ MI
    1 N gs ns hgs B hB
  filter_upwards [hgs.eventually_ge_atTop 2,
    hgood.eventually (gt_mem_nhds (ENNReal.lt_add_right hK one_ne_zero)),
    hbad.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hthird)),
    hsep.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hthird))]
    with j hj hjgood hjbad hjsep
  have htail:= (ENNReal.div_le_div_right hjgood.le ((N+1:ℕ):ℝ≥0∞)).trans hN.le
  have hb:=full_prefix_failure_measure_le A MI (gs j) (ns j) hj B N
  apply hb.trans ((add_le_add (add_le_add hjbad.le htail) hjsep.le).trans_eq ?_)
  rw [←ENNReal.ofReal_add hthird.le hthird.le,
    ←ENNReal.ofReal_add (by positivity) hthird.le]
  have heq : (ζ.toReal/3+ζ.toReal/3)+ζ.toReal/3=ζ.toReal := by ring
  rw [heq,ENNReal.ofReal_toReal hζtop]


theorem full_prefix_connected_measure_tendsto_one (T : TightRegions G)
    (BZ : BuddZonneveldTransform G T) (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (D : BuddLionsTightGeometry G T H Q A)
    (BM : ∀g n,(hg : 2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop) (B : ℝ) (hB : 0≤B) :
    Tendsto (fun j=>TightConnected.connectedCuspProbability G (gs j) (ns j)
      {X | FullPrefixConnected Q A X (B/tightScale ((ns j:ℝ)/(gs j)))}) atTop (𝓝 1) := by
  have hfail:=full_prefix_connected_failure_measure_tendsto_zero T BZ Q A MI D BM gs ns hgs B hB
  have hprob:=connected_cusp_probability_eventually_probability gs ns hgs (G:=G)
  have hlow : Tendsto (fun j=>(1:ℝ≥0∞)-TightConnected.connectedCuspProbability G (gs j) (ns j)
      {X | ¬FullPrefixConnected Q A X (B/tightScale ((ns j:ℝ)/(gs j)))}) atTop (𝓝 1) := by
    simpa only [tsub_zero] using
      ENNReal.Tendsto.sub tendsto_const_nhds hfail (Or.inl (by simp))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [hprob] with j hj
    let:=hj
    apply tsub_le_iff_right.mpr
    have h := measure_union_le
      {X | FullPrefixConnected Q A X (B/tightScale ((ns j:ℝ)/(gs j)))}
      {X | ¬FullPrefixConnected Q A X (B/tightScale ((ns j:ℝ)/(gs j)))}
      (μ:=TightConnected.connectedCuspProbability G (gs j) (ns j))
    have he : ({X : TightSurface G (gs j) 0 (ns j) (fun _=>0) (fun _=>0) | FullPrefixConnected Q A X (B/tightScale ((ns j:ℝ)/(gs j)))} ∪
        {X | ¬FullPrefixConnected Q A X (B/tightScale ((ns j:ℝ)/(gs j)))})=Set.univ := by
      ext X
      simp only [Set.mem_union,Set.mem_setOf_eq,Set.mem_univ,iff_true]
      exact em _
    simpa only [he,measure_univ] using h
  · filter_upwards [hprob] with j hj
    let:=hj
    exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ

theorem full_prefix_simple_disjoint_connected_probability_tendsto_one (T : TightRegions G)
    (BZ : BuddZonneveldTransform G T) (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (D : BuddLionsTightGeometry G T H Q A)
    (BM : ∀g n,(hg : 2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop) (B : ℝ) (hB : 0≤B) :
    Tendsto (fun j=>TightConnected.connectedCuspProbability G (gs j) (ns j)
      {X | ¬BadConfiguration Q X (B/tightScale ((ns j:ℝ)/(gs j))) ∧
        FullPrefixConnected Q A X (B/tightScale ((ns j:ℝ)/(gs j)))}) atTop (𝓝 1) := by
  apply (full_prefix_connected_measure_tendsto_one T BZ Q A MI D BM gs ns hgs B hB).congr'
  apply Eventually.of_forall
  intro j
  have hs : {X : TightSurface G (gs j) 0 (ns j) (fun _=>0) (fun _=>0) |
      FullPrefixConnected Q A X (B/tightScale ((ns j:ℝ)/(gs j)))} =
      {X | ¬BadConfiguration Q X (B/tightScale ((ns j:ℝ)/(gs j))) ∧
        FullPrefixConnected Q A X (B/tightScale ((ns j:ℝ)/(gs j)))} := by
    ext X
    exact ⟨fun h=>⟨full_prefix_connected_not_bad A X _ h,h⟩,fun h=>h.2⟩
  exact congrArg (fun s=>TightConnected.connectedCuspProbability G (gs j) (ns j) s) hs

end WP.Tight
