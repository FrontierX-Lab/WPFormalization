import WPFormalization.Critical.CutBadFamilyBounds
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External CutGraphOrbits MeasureTheory Filter Finset
open scoped ENNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  (MI : MirzakhaniIntegration G H T) {g n t Q : ℕ}

include MI in
lemma critical_ordered_marked_half_estimate_regime
    (k Q u v w : ℕ) (hk : 1≤k) (hQ : 1≤Q) (L : ℝ) (hL : 0≤L)
    (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    ∃C : ℝ,0<C ∧ ∀ᶠ g : ℕ in atTop,∀S : CutSkeleton k Q,S.Connected →
      (∫⁻ X,cutMarkedPartitionCount T S (g:=g) (n:=n g) u v w L X
        ∂wpProbability G g (n g))≤ENNReal.ofReal (C*(g:ℝ)^(-1/2:ℝ)) := by
  by_cases hw : 1≤w
  · obtain ⟨C,hC,hb⟩ := critical_cut_marked_estimate_regime G T MI k Q u v w hk hQ L hL n c hc hn
    refine ⟨C,hC,?_⟩
    filter_upwards [hb,eventually_ge_atTop (1:ℕ)] with g hg hg1
    intro S hS
    refine (hg S hS).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hwR : (1:ℝ)≤w := by exact_mod_cast hw
    have hvR : (0:ℝ)≤v := Nat.cast_nonneg _
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hg1) (by linarith)
  · have hw0 : w=0 := by omega
    subst w
    refine ⟨1,by norm_num,?_⟩
    filter_upwards [eventually_ge_atTop (k+2)] with g hg
    intro S hS
    simp only [cutMarkedPartitionCount,markedPartitionOrbits_zero_stable T S u v hg,
      sum_empty,lintegral_zero]
    exact bot_le

include MI in
lemma critical_ordered_marked_tendsto_zero
    (k Q u v w : ℕ) (hk : 1≤k) (hQ : 1≤Q) (L : ℝ) (hL : 0≤L)
    (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (S : CutSkeleton k Q) (hS : S.Connected) :
    Tendsto (fun g : ℕ => ∫⁻ X,cutMarkedPartitionCount T S u v w L X
      ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := critical_ordered_marked_half_estimate_regime T MI k Q u v w hk hQ L hL n c hc hn
  have ht : Tendsto (fun g : ℕ => ENNReal.ofReal (C*(g:ℝ)^(-1/2:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_const_nhds.mul critical_half_power_tendsto_zero)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall (fun _ => bot_le)) (hb.mono (fun _ hg => hg S hS))

def markedPartitionFamilyCount (S : CutSkeleton t Q) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑p : Fin (Q+1)×(Fin (Q+1)×Fin (Q+1)),cutMarkedPartitionCount T S p.1.val p.2.1.val p.2.2.val L X

include MI in
lemma markedPartitionFamilyCount_measurable (S : CutSkeleton t Q) (L : ℝ) :
    Measurable (markedPartitionFamilyCount T S (g:=g) (n:=n) L) := by
  apply Finset.measurable_sum
  intro p hp
  exact cutMarkedPartitionCount_measurable T MI S p.1.val p.2.1.val p.2.2.val L

include MI in
lemma critical_markedPartitionFamilyCount_tendsto_zero
    (ht : 1≤t) (hQ : 1≤Q) (S : CutSkeleton t Q) (hS : S.Connected)
    (L : ℝ) (hL : 0≤L) (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g : ℕ => ∫⁻ X,markedPartitionFamilyCount T S L X
      ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  have hlin (g : ℕ) : (∫⁻ X,markedPartitionFamilyCount T S L X ∂wpProbability G g (n g))=
      ∑p : Fin (Q+1)×(Fin (Q+1)×Fin (Q+1)),
        ∫⁻ X,cutMarkedPartitionCount T S p.1.val p.2.1.val p.2.2.val L X ∂wpProbability G g (n g) := by
    unfold markedPartitionFamilyCount
    apply lintegral_finsetSum
    intro p hp
    exact cutMarkedPartitionCount_measurable T MI S p.1.val p.2.1.val p.2.2.val L
  simp_rw [hlin]
  have hz : 𝓝 (∑_p : Fin (Q+1)×(Fin (Q+1)×Fin (Q+1)),(0 : ℝ≥0∞))=𝓝 (0 : ℝ≥0∞) := by simp
  rw [←hz]
  apply tendsto_finsetSum
  intro p hp
  exact critical_ordered_marked_tendsto_zero T MI t Q p.1.val p.2.1.val p.2.2.val ht hQ L hL n c hc hn S hS

def markedCutFamilyCount (t : ℕ) (L : ℝ) (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑q : Fin (2*t+1),if 1≤q.val then
    ∑S : {S : CutSkeleton t q.val // S.Connected},markedPartitionFamilyCount T S.val L X else 0

include MI in
lemma markedCutFamilyCount_measurable (t : ℕ) (L : ℝ) :
    Measurable (markedCutFamilyCount T t L (g:=g) (n:=n)) := by
  apply Finset.measurable_sum
  intro q hq
  by_cases hQ : 1≤q.val
  · simp only [ite_eq_left hQ]
    apply Finset.measurable_sum
    intro S hS
    exact markedPartitionFamilyCount_measurable T MI S.val L
  · simp only [ite_eq_right hQ]
    exact measurable_const

include MI in
lemma critical_markedCutFamilyCount_tendsto_zero
    (t : ℕ) (ht : 1≤t) (L : ℝ) (hL : 0≤L) (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g : ℕ => ∫⁻ X,markedCutFamilyCount T t L X ∂wpProbability G g (n g))
      atTop (𝓝 0) := by
  have hlin (g : ℕ) : (∫⁻ X,markedCutFamilyCount T t L X ∂wpProbability G g (n g))=
      ∑q : Fin (2*t+1),if 1≤q.val then
        ∑S : {S : CutSkeleton t q.val // S.Connected},
          ∫⁻ X,markedPartitionFamilyCount T S.val L X ∂wpProbability G g (n g) else 0 := by
    unfold markedCutFamilyCount
    rw [lintegral_finsetSum]
    · apply sum_congr rfl
      intro q hq
      by_cases hQ : 1≤q.val
      · simp only [ite_eq_left hQ]
        apply lintegral_finsetSum
        intro S hS
        exact markedPartitionFamilyCount_measurable T MI S.val L
      · simp only [ite_eq_right hQ,lintegral_zero]
    · intro q hq
      by_cases hQ : 1≤q.val
      · simp only [ite_eq_left hQ]
        exact Finset.measurable_sum univ (fun S _ => markedPartitionFamilyCount_measurable T MI S.val L)
      · simp only [ite_eq_right hQ]
        exact measurable_const
  simp_rw [hlin]
  have hz : 𝓝 (∑_q : Fin (2*t+1),(0 : ℝ≥0∞))=𝓝 (0 : ℝ≥0∞) := by simp
  rw [←hz]
  apply tendsto_finsetSum
  intro q hq
  by_cases hQ : 1≤q.val
  · simp only [ite_eq_left hQ]
    have hzs : 𝓝 (∑_S : {S : CutSkeleton t q.val // S.Connected},(0 : ℝ≥0∞))=𝓝 (0 : ℝ≥0∞) := by simp
    rw [←hzs]
    apply tendsto_finsetSum
    intro S hS
    exact critical_markedPartitionFamilyCount_tendsto_zero T MI ht hQ S.val S.property L hL n c hc hn
  · simpa only [ite_eq_right hQ] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
end WP.Critical
