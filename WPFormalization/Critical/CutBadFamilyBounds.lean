import WPFormalization.Critical.CutNonSurviving
import WPFormalization.Critical.CutFiniteSkeletonCover
import WPFormalization.Critical.CutCountMeasurable
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External CutGraphOrbits MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  {g n t Q : ℕ}

def badPartitionCount (S : CutSkeleton t Q) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑ p : Fin (Q+1)×(Fin (Q+1)×Fin (Q+1)),
    if p.2.2.val≠1 ∨ p.2.1.val≠0 then
      cutPartitionCount T S p.1.val p.2.1.val p.2.2.val L X else 0

include T in
lemma badPartitionCount_measurable (MI : MirzakhaniIntegration G H T)
    (S : CutSkeleton t Q) (L : ℝ) : Measurable (badPartitionCount T S (g:=g) (n:=n) L) := by
  apply Finset.measurable_sum
  intro p hp
  by_cases hb : p.2.2.val≠1 ∨ p.2.1.val≠0
  · simpa only [ite_eq_left hb] using cutPartitionCount_measurable T MI S p.1.val p.2.1.val p.2.2.val L
  · simp only [ite_eq_right hb]
    exact measurable_const

lemma critical_badPartitionCount_tendsto_zero (MI : MirzakhaniIntegration G H T)
    (ht : 1≤t) (hQ : 1≤Q) (S : CutSkeleton t Q) (hS : S.Connected)
    (L : ℝ) (hL : 0≤L) (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g : ℕ => ∫⁻ X, badPartitionCount T S L X
      ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  have hlin (g : ℕ) : (∫⁻ X, badPartitionCount T S L X ∂wpProbability G g (n g))=
      ∑p : Fin (Q+1)×(Fin (Q+1)×Fin (Q+1)),
        if p.2.2.val≠1 ∨ p.2.1.val≠0 then
          (∫⁻ X,cutPartitionCount T S p.1.val p.2.1.val p.2.2.val L X ∂wpProbability G g (n g)) else 0 := by
    unfold badPartitionCount
    rw [lintegral_finsetSum]
    · apply sum_congr rfl
      intro p hp
      by_cases hb : p.2.2.val≠1 ∨ p.2.1.val≠0 <;> simp only [hb,ite_true,ite_false,lintegral_zero]
    · intro p hp
      by_cases hb : p.2.2.val≠1 ∨ p.2.1.val≠0
      · simpa only [ite_eq_left hb] using (cutPartitionCount_measurable T MI S p.1.val p.2.1.val p.2.2.val L)
      · simp only [ite_eq_right hb]
        exact measurable_const
  simp_rw [hlin]
  have hz : 𝓝 (∑_p : Fin (Q+1)×(Fin (Q+1)×Fin (Q+1)),(0 : ℝ≥0∞))=𝓝 (0 : ℝ≥0∞) := by simp
  rw [←hz]
  apply tendsto_finsetSum
  intro p hp
  by_cases hb : p.2.2.val≠1 ∨ p.2.1.val≠0
  · simpa only [ite_eq_left hb] using critical_ordered_nonSurviving_tendsto_zero G T MI t Q
      p.1.val p.2.1.val p.2.2.val ht hQ hb L hL n c hc hn S hS
  · simpa only [ite_eq_right hb] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

def badCutFamilyCount (t : ℕ) (L : ℝ) (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑ q : Fin (2*t+1), if 1≤q.val then
    ∑ S : {S : CutSkeleton t q.val // S.Connected},badPartitionCount T S.val L X else 0

lemma critical_badCutFamilyCount_tendsto_zero (MI : MirzakhaniIntegration G H T)
    (t : ℕ) (ht : 1≤t) (L : ℝ) (hL : 0≤L) (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g : ℕ => ∫⁻ X,badCutFamilyCount T t L X ∂wpProbability G g (n g))
      atTop (𝓝 0) := by
  have hlin (g : ℕ) : (∫⁻ X,badCutFamilyCount T t L X ∂wpProbability G g (n g))=
    ∑q : Fin (2*t+1), if 1≤q.val then
      ∑S : {S : CutSkeleton t q.val // S.Connected},
        ∫⁻ X,badPartitionCount T S.val L X ∂wpProbability G g (n g) else 0 := by
    unfold badCutFamilyCount
    rw [lintegral_finsetSum]
    · apply sum_congr rfl
      intro q hq
      by_cases hQ : 1≤q.val
      · simp only [ite_eq_left hQ]
        apply lintegral_finsetSum
        intro S hS
        exact (badPartitionCount_measurable T MI S.val L)
      · simp only [ite_eq_right hQ,lintegral_zero]
    · intro q hq
      by_cases hQ : 1≤q.val
      · simp only [ite_eq_left hQ]
        exact (Finset.measurable_sum univ (fun (S : {S : CutSkeleton t q.val // S.Connected}) _ => badPartitionCount_measurable T MI S.val L))
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
    exact critical_badPartitionCount_tendsto_zero T MI ht hQ S.val S.property L hL n c hc hn
  · simpa only [ite_eq_right hQ] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
end WP.Critical
