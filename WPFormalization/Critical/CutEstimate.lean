import WPFormalization.Critical.CutCriticalCuts
import WPFormalization.Critical.CutPartitionCover

noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.CutGraphOrbits
open WP.External Finset MeasureTheory
open scoped ENNReal Classical
universe uu vv ww zz

def FitsPartition {g n k Q u v w : ℕ} (S : CutSkeleton k Q)
    (R : CutVertexPartition Q u v w) (a : BoundedAllocation g n Q) : Prop :=
  (∀ i, S.degree (R.oneVertex i)=1) ∧ (∀ i, S.degree (R.twoVertex i)=2) ∧
    PartitionAdmissible S R a

def HasPartition {g n k Q : ℕ} (S : CutSkeleton k Q) (u v w : ℕ)
    (a : BoundedAllocation g n Q) : Prop := ∃ R : CutVertexPartition Q u v w, FitsPartition S R a

def HasMarkedPartition {g n k Q : ℕ} (S : CutSkeleton k Q) (u v w : ℕ)
    (a : BoundedAllocation g n Q) : Prop :=
  ∃ b : CutVertexPartition Q u v w × Fin u, FitsPartition S b.1 a ∧
    3 ≤ cutCuspHistogram a.2 (b.1.oneVertex b.2)

lemma critical_cut_all_partitions_expectation {P : PsiTheory}
    (G : WeilPeterssonGeometry.{uu,vv} P) {H : HyperbolicCurveGeometry.{uu,vv,ww} G}
    (T : MulticurveTopology.{uu,vv,ww,zz} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hw : 1 ≤ w)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      ∀ s : Finset (Orbits T S (g:=g) (n:=n)),
      (∀ o ∈ s, HasPartition S u v w (boundedAllocation T S o)) →
      (∑ o ∈ s, ∫⁻ X, T.orbitSum o.val (cutLengthTest k L) X ∂wpProbability G g n) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2)) := by
  classical
  obtain ⟨C,hC,G₀,hr⟩ := critical_cut_partition_expectation G T MI k Q u v w hk hQ hw A L hA hL
  let d : ℝ := Fintype.card (CutVertexPartition Q u v w)+1
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨d*C,mul_pos hd hC,G₀,?_⟩
  intro g hg n hn hcritical S hS s hs
  let f : Orbits T S (g:=g) (n:=n) → ℝ≥0∞ := fun o =>
    ∫⁻ X, T.orbitSum o.val (cutLengthTest k L) X ∂wpProbability G g n
  have hc := cut_partition_sum_cover_bound s
    (fun R o => FitsPartition S R (boundedAllocation T S o)) hs f
    (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2)) (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hb : ∀ R : CutVertexPartition Q u v w,
      (∑ o ∈ s.filter (fun o => FitsPartition S R (boundedAllocation T S o)), f o) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2)) := by
    intro R
    by_cases hdeg : (∀ i, S.degree (R.oneVertex i)=1) ∧ (∀ i, S.degree (R.twoVertex i)=2)
    · exact hr g hg n hn hcritical S hS R hdeg.1 hdeg.2 _
        (fun o ho => (mem_filter.mp ho).2.2.2)
    · have he : s.filter (fun o => FitsPartition S R (boundedAllocation T S o))=∅ := by
        apply filter_eq_empty_iff.mpr
        intro o ho hfit
        exact hdeg ⟨hfit.1,hfit.2.1⟩
      simp only [he,sum_empty]
      exact bot_le
  have hc' := hc (fun b => by
    convert hb b using 1 <;> congr 1 <;> ext o <;> simp)
  convert hc' using 1 <;> dsimp [d] <;> ring

lemma critical_cut_all_marked_partitions_expectation {P : PsiTheory}
    (G : WeilPeterssonGeometry.{uu,vv} P) {H : HyperbolicCurveGeometry.{uu,vv,ww} G}
    (T : MulticurveTopology.{uu,vv,ww,zz} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hw : 1 ≤ w)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      ∀ s : Finset (Orbits T S (g:=g) (n:=n)),
      (∀ o ∈ s, HasMarkedPartition S u v w (boundedAllocation T S o)) →
      (∑ o ∈ s, ∫⁻ X, T.orbitSum o.val (cutLengthTest k L) X ∂wpProbability G g n) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2)) := by
  classical
  obtain ⟨C,hC,G₀,hr⟩ := critical_cut_marked_partition_expectation G T MI k Q u v w hk hQ hw A L hA hL
  let d : ℝ := Fintype.card (CutVertexPartition Q u v w × Fin u)+1
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨d*C,mul_pos hd hC,G₀,?_⟩
  intro g hg n hn hcritical S hS s hs
  let f : Orbits T S (g:=g) (n:=n) → ℝ≥0∞ := fun o =>
    ∫⁻ X, T.orbitSum o.val (cutLengthTest k L) X ∂wpProbability G g n
  have hc := cut_partition_sum_cover_bound s
    (fun (b : CutVertexPartition Q u v w × Fin u) o => FitsPartition S b.1 (boundedAllocation T S o) ∧
      3 ≤ cutCuspHistogram (boundedAllocation T S o).2 (b.1.oneVertex b.2)) hs f
    (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2)) (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hb : ∀ b : CutVertexPartition Q u v w × Fin u,
      (∑ o ∈ s.filter (fun o => FitsPartition S b.1 (boundedAllocation T S o) ∧
        3 ≤ cutCuspHistogram (boundedAllocation T S o).2 (b.1.oneVertex b.2)), f o) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2)) := by
    intro b
    by_cases hdeg : (∀ i, S.degree (b.1.oneVertex i)=1) ∧ (∀ i, S.degree (b.1.twoVertex i)=2)
    · exact hr g hg n hn hcritical S hS b.1 hdeg.1 hdeg.2 b.2 _
        (fun o ho => ⟨(mem_filter.mp ho).2.1.2.2,(mem_filter.mp ho).2.2⟩)
    · have he : s.filter (fun o => FitsPartition S b.1 (boundedAllocation T S o) ∧
          3 ≤ cutCuspHistogram (boundedAllocation T S o).2 (b.1.oneVertex b.2))=∅ := by
        apply filter_eq_empty_iff.mpr
        intro o ho hfit
        exact hdeg ⟨hfit.1.1,hfit.1.2.1⟩
      simp only [he,sum_empty]
      exact bot_le
  have hc' := hc (fun b => by
    convert hb b using 1 <;> congr 1 <;> ext o <;> simp)
  convert hc' using 1 <;> dsimp [d] <;> ring
end WP.Critical.CutGraphOrbits
