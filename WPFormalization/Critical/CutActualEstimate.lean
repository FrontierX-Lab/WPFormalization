import WPFormalization.Critical.CutEstimate
import WPFormalization.Critical.CutRealizationTransport
import WPFormalization.Critical.CutVertexPartition
noncomputable section
namespace WP.Critical
open WP.External
namespace CutVertexPartition
variable {Q Q' u v w : ℕ}
def transport (R : CutVertexPartition Q u v w) (e : Fin Q ≃ Fin Q') :
    CutVertexPartition Q' u v w := ⟨e.symm.trans R.vertices⟩
@[simp] lemma transport_oneVertex (R : CutVertexPartition Q u v w) (e : Fin Q ≃ Fin Q') (i : Fin u) :
    (R.transport e).oneVertex i = e (R.oneVertex i) := rfl
@[simp] lemma transport_twoVertex (R : CutVertexPartition Q u v w) (e : Fin Q ≃ Fin Q') (i : Fin v) :
    (R.transport e).twoVertex i = e (R.twoVertex i) := rfl
@[simp] lemma transport_stableVertex (R : CutVertexPartition Q u v w) (e : Fin Q ≃ Fin Q') (i : Fin w) :
    (R.transport e).stableVertex i = e (R.stableVertex i) := rfl
end CutVertexPartition

def CutDataFitsPartition {n k u v w : ℕ} (D : MulticurveCutData n k)
    (R : CutVertexPartition D.components u v w) : Prop :=
  (∀ i, D.genus (R.oneVertex i)=0 ∧ CutGraphData.degree D (R.oneVertex i)=1) ∧
  (∀ i, D.genus (R.twoVertex i)=0 ∧ CutGraphData.degree D (R.twoVertex i)=2) ∧
  (∀ i, Stable (D.genus (R.stableVertex i)) (CutGraphData.degree D (R.stableVertex i)))

def CutDataHasPartition {n k : ℕ} (D : MulticurveCutData n k) (u v w : ℕ) : Prop :=
  ∃ R : CutVertexPartition D.components u v w, CutDataFitsPartition D R

def CutDataHasMarkedPartition {n k : ℕ} (D : MulticurveCutData n k) (u v w : ℕ) : Prop :=
  ∃ (R : CutVertexPartition D.components u v w) (i₀ : Fin u),
    CutDataFitsPartition D R ∧ 3 ≤ CutGraphData.cuspCount D (R.oneVertex i₀)
end WP.Critical
namespace WP.Critical.CutGraphOrbits
open WP.External
universe uu vv ww zz
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{uu,vv} P}
  {H : HyperbolicCurveGeometry.{uu,vv,ww} G} (T : MulticurveTopology.{uu,vv,ww,zz} G H)
  {g n k Q u v w : ℕ} (S : CutSkeleton k Q)

lemma actual_partition_canonical (o : Orbits T S (g:=g) (n:=n))
    (h : CutDataHasPartition (T.cut o.val) u v w) :
    HasPartition S u v w (boundedAllocation T S o) := by
  obtain ⟨R,hR⟩ := h
  let q := realization T S o
  refine ⟨R.transport q.vertices,?_,?_,?_,?_,?_⟩
  · intro i
    rw [CutVertexPartition.transport_oneVertex,←q.degree_eq]
    exact (hR.1 i).2
  · intro i
    rw [CutVertexPartition.transport_twoVertex,←q.degree_eq]
    exact (hR.2.1 i).2
  · intro i
    change q.genus ((R.transport q.vertices).oneVertex i)=0
    simpa only [CutVertexPartition.transport_oneVertex,CutSkeleton.Realization.genus,
      Equiv.symm_apply_apply] using (hR.1 i).1
  · intro i
    change q.genus ((R.transport q.vertices).twoVertex i)=0
    simpa only [CutVertexPartition.transport_twoVertex,CutSkeleton.Realization.genus,
      Equiv.symm_apply_apply] using (hR.2.1 i).1
  · intro i
    change Stable (q.genus ((R.transport q.vertices).stableVertex i))
      (S.degree ((R.transport q.vertices).stableVertex i))
    simp only [CutVertexPartition.transport_stableVertex,CutSkeleton.Realization.genus,
      Equiv.symm_apply_apply]
    rw [←q.degree_eq]
    exact hR.2.2 i

lemma actual_marked_partition_canonical (o : Orbits T S (g:=g) (n:=n))
    (h : CutDataHasMarkedPartition (T.cut o.val) u v w) :
    HasMarkedPartition S u v w (boundedAllocation T S o) := by
  obtain ⟨R,i₀,hR,hcusps⟩ := h
  let q := realization T S o
  -- Retain the same transported named leaf rather than choosing another partition.
  have hfit : FitsPartition S (R.transport q.vertices) (boundedAllocation T S o) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i
      rw [CutVertexPartition.transport_oneVertex,←q.degree_eq]
      exact (hR.1 i).2
    · intro i
      rw [CutVertexPartition.transport_twoVertex,←q.degree_eq]
      exact (hR.2.1 i).2
    · intro i
      change q.genus ((R.transport q.vertices).oneVertex i)=0
      simpa only [CutVertexPartition.transport_oneVertex,CutSkeleton.Realization.genus,
        Equiv.symm_apply_apply] using (hR.1 i).1
    · intro i
      change q.genus ((R.transport q.vertices).twoVertex i)=0
      simpa only [CutVertexPartition.transport_twoVertex,CutSkeleton.Realization.genus,
        Equiv.symm_apply_apply] using (hR.2.1 i).1
    · intro i
      change Stable (q.genus ((R.transport q.vertices).stableVertex i))
        (S.degree ((R.transport q.vertices).stableVertex i))
      simp only [CutVertexPartition.transport_stableVertex,CutSkeleton.Realization.genus,
        Equiv.symm_apply_apply]
      rw [←q.degree_eq]
      exact hR.2.2 i
  refine ⟨⟨R.transport q.vertices,i₀⟩,hfit,?_⟩
  change 3 ≤ cutCuspHistogram q.cusps ((R.transport q.vertices).oneVertex i₀)
  rw [CutVertexPartition.transport_oneVertex,←q.cuspCount_eq]
  exact hcusps
end WP.Critical.CutGraphOrbits

universe aa bb cc dd
namespace WP.Critical.CutGraphOrbits
open WP.External Finset MeasureTheory
open scoped ENNReal Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  {g n k Q : ℕ} (S : CutSkeleton k Q)

/-- Every actual ordered cut orbit of the fixed graph having the stated
vertex types is included, over all admissible genera and labelled cusps. -/
def partitionOrbits (u v w : ℕ) : Finset (Orbits T S (g:=g) (n:=n)) := by
  classical
  letI : Finite (Orbits T S (g:=g) (n:=n)) :=
    Finite.of_injective (boundedAllocation T S) (boundedAllocation_injective T S)
  letI := Fintype.ofFinite (Orbits T S (g:=g) (n:=n))
  exact univ.filter (fun o => CutDataHasPartition (T.cut o.val) u v w)
def markedPartitionOrbits (u v w : ℕ) : Finset (Orbits T S (g:=g) (n:=n)) := by
  classical
  letI : Finite (Orbits T S (g:=g) (n:=n)) :=
    Finite.of_injective (boundedAllocation T S) (boundedAllocation_injective T S)
  letI := Fintype.ofFinite (Orbits T S (g:=g) (n:=n))
  exact univ.filter (fun o => CutDataHasMarkedPartition (T.cut o.val) u v w)

lemma mem_partitionOrbits (u v w : ℕ) (o : Orbits T S (g:=g) (n:=n)) :
    o ∈ partitionOrbits T S u v w ↔ CutDataHasPartition (T.cut o.val) u v w := by
  classical
  simp [partitionOrbits]
lemma mem_markedPartitionOrbits (u v w : ℕ) (o : Orbits T S (g:=g) (n:=n)) :
    o ∈ markedPartitionOrbits T S u v w ↔ CutDataHasMarkedPartition (T.cut o.val) u v w := by
  classical
  simp [markedPartitionOrbits]

/-- Actual ordered multicurve count with every cut length at most L. It is a
finite sum of the classical geometric orbit sums, not a recurrence model. -/
def cutPartitionCount (u v w : ℕ) (L : ℝ) (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑ o ∈ partitionOrbits T S u v w, T.orbitSum o.val (cutLengthTest k L) X
def cutMarkedPartitionCount (u v w : ℕ) (L : ℝ) (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑ o ∈ markedPartitionOrbits T S u v w, T.orbitSum o.val (cutLengthTest k L) X

lemma partition_requires_stable_vertex (u v w : ℕ) (hg : k+2 ≤ g)
    (o : Orbits T S (g:=g) (n:=n)) (ho : CutDataHasPartition (T.cut o.val) u v w) : 1 ≤ w := by
  by_contra hw
  have hw0 : w=0 := by omega
  subst w
  obtain ⟨R,hR⟩ := ho
  have hzero : ∀ c : Fin (T.cut o.val).components, (T.cut o.val).genus c=0 := by
    intro c
    obtain ⟨t,rfl⟩ := R.vertices.symm.surjective c
    rcases t with i | i | i
    · exact (hR.1 i).1
    · exact (hR.2.1 i).1
    · exact Fin.elim0 i
  have he := T.cut_euler o.val
  simp only [hzero,sum_const_zero] at he
  omega

lemma partitionOrbits_zero_stable (u v : ℕ) (hg : k+2 ≤ g) :
    partitionOrbits T S (g:=g) (n:=n) u v 0=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro o ho
  have := partition_requires_stable_vertex T S u v 0 hg o ((mem_partitionOrbits T S u v 0 o).mp ho)
  omega
lemma markedPartitionOrbits_zero_stable (u v : ℕ) (hg : k+2 ≤ g) :
    markedPartitionOrbits T S (g:=g) (n:=n) u v 0=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro o ho
  obtain ⟨R,i₀,hR,hq⟩ := (mem_markedPartitionOrbits T S u v 0 o).mp ho
  have := partition_requires_stable_vertex T S u v 0 hg o ⟨R,hR⟩
  omega
end WP.Critical.CutGraphOrbits

namespace WP.Critical
open WP.External Finset MeasureTheory CutGraphOrbits
open scoped ENNReal Classical

/- Strong uniform form of Lemma G.1: actual ordered multicurves of the
specified graph, allowing every marking of its prescribed vertex types.
Consequently any particular specified graph partition satisfies this bound. -/
@[blueprint "lem:critical-cuts"]
theorem critical_cut_estimate {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, cutPartitionCount T S (g:=g) (n:=n) u v w L X ∂wpProbability G g n) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2)) := by
  classical
  by_cases hw : 1 ≤ w
  · obtain ⟨C,hC,G₀,hr⟩ := critical_cut_all_partitions_expectation G T MI k Q u v w hk hQ hw A L hA hL
    refine ⟨C,hC,G₀,?_⟩
    intro g hg n hn hcritical S hS
    unfold cutPartitionCount
    rw [lintegral_finsetSum _ (fun o _ => MI.orbitSum_measurable o.val _ (cutLengthTest_measurable k L))]
    exact hr g hg n hn hcritical S hS _ (fun o ho =>
      actual_partition_canonical T S o ((mem_partitionOrbits T S u v w o).mp ho))
  · have hw0 : w=0 := by omega
    subst w
    refine ⟨1,by norm_num,k+2,?_⟩
    intro g hg n hn hcritical S hS
    simp only [cutPartitionCount,partitionOrbits_zero_stable T S u v hg,sum_empty,lintegral_zero]
    exact bot_le

/- The actual count with some designated (0,1) leaf receiving at least three
original cusps has the extra inverse-square-root factor of Lemma G.1. The
union over its finitely many possible designations gives a stronger bound. -/
@[blueprint "lem:critical-cuts"]
theorem critical_cut_marked_estimate {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, cutMarkedPartitionCount T S (g:=g) (n:=n) u v w L X ∂wpProbability G g n) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2)) := by
  classical
  by_cases hw : 1 ≤ w
  · obtain ⟨C,hC,G₀,hr⟩ := critical_cut_all_marked_partitions_expectation G T MI k Q u v w hk hQ hw A L hA hL
    refine ⟨C,hC,G₀,?_⟩
    intro g hg n hn hcritical S hS
    unfold cutMarkedPartitionCount
    rw [lintegral_finsetSum _ (fun o _ => MI.orbitSum_measurable o.val _ (cutLengthTest_measurable k L))]
    exact hr g hg n hn hcritical S hS _ (fun o ho =>
      actual_marked_partition_canonical T S o ((mem_markedPartitionOrbits T S u v w o).mp ho))
  · have hw0 : w=0 := by omega
    subst w
    refine ⟨1,by norm_num,k+2,?_⟩
    intro g hg n hn hcritical S hS
    simp only [cutMarkedPartitionCount,markedPartitionOrbits_zero_stable T S u v hg,sum_empty,lintegral_zero]
    exact bot_le
end WP.Critical
