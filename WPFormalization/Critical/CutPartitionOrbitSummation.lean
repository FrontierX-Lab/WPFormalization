import WPFormalization.Critical.CutOrbitSummation
import WPFormalization.Critical.CutVertexPartition
import WPFormalization.Critical.CutCuspLabels
import WPFormalization.Critical.CutSkeletonDegree

/-! Leaf-zero fixed-skeleton allocations reindex injectively into the actual
stable genus vectors while all original cusp labels and any selection remain.
The positive Gamma sum increases only by dropping finite physical restrictions. -/
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical
open WP.External Finset
open scoped Classical

namespace CutVertexPartition
variable {Q u v w : ℕ} (R : CutVertexPartition Q u v w)

lemma genusVector_eq_of_leaf_zero (a : Fin Q → ℕ)
    (h01 : ∀ i, a (R.oneVertex i)=0) (h02 : ∀ i, a (R.twoVertex i)=0) :
    R.genusVector (fun i => a (R.stableVertex i)) = a := by
  funext c
  obtain ⟨j,rfl⟩ := R.vertices.symm.surjective c
  rcases j with i | i | i
  · simpa only [genusVector,R.vertices.apply_symm_apply,oneVertex] using (h01 i).symm
  · simpa only [genusVector,R.vertices.apply_symm_apply,twoVertex] using (h02 i).symm
  · simp only [genusVector,R.vertices.apply_symm_apply,stableVertex]

end CutVertexPartition
namespace CutGraphOrbits
variable {g n k Q u v w : ℕ}

def stableGenera (R : CutVertexPartition Q u v w) (a : BoundedAllocation g n Q) : Fin w → ℕ :=
  fun i => (a.1 (R.stableVertex i)).val

lemma allocationCutData_boundaryCount (S : CutSkeleton k Q) (a : BoundedAllocation g n Q)
    (c : Fin Q) :
    (allocationCutData S a).boundaryCount c = S.degree c+cutCuspHistogram a.2 c := by
  exact (S.boundaryCount_cuspHistogram (fun c => (a.1 c).val) a.2 c).trans (Nat.add_comm _ _)

lemma allocationGamma_eq_histogram (S : CutSkeleton k Q) (a : BoundedAllocation g n Q) :
    allocationGamma S a = ∏ c : Fin Q,
      Real.Gamma (complexity (a.1 c).val (S.degree c+cutCuspHistogram a.2 c)) := by
  unfold allocationGamma
  simp_rw [allocationCutData_boundaryCount]

lemma stableGenera_recover (R : CutVertexPartition Q u v w) (a : BoundedAllocation g n Q)
    (h01 : ∀ i, (a.1 (R.oneVertex i)).val=0)
    (h02 : ∀ i, (a.1 (R.twoVertex i)).val=0) :
    R.genusVector (stableGenera R a) = fun c => (a.1 c).val :=
  R.genusVector_eq_of_leaf_zero (fun c => (a.1 c).val) h01 h02

/-- Every individual original cusp label survives the genus-vector reduction.
Only the two fixed-zero leaf genera are omitted. -/
lemma stableGenera_cusps_injOn (R : CutVertexPartition Q u v w)
    (s : Finset (BoundedAllocation g n Q))
    (h01 : ∀ a ∈ s, ∀ i, (a.1 (R.oneVertex i)).val=0)
    (h02 : ∀ a ∈ s, ∀ i, (a.1 (R.twoVertex i)).val=0) :
    Set.InjOn (fun a : BoundedAllocation g n Q => (stableGenera R a,a.2)) s := by
  intro a ha b hb he
  have hs : stableGenera R a=stableGenera R b := congrArg Prod.fst he
  have hσ : a.2=b.2 :=
    congrArg (fun b : (Fin w → ℕ) × (Fin n → Fin Q) => b.2) he
  apply Prod.ext _ hσ
  funext c
  apply Fin.ext
  have hga := stableGenera_recover R a (h01 a ha) (h02 a ha)
  have hgb := stableGenera_recover R b (h01 b hb) (h02 b hb)
  exact congrFun (hga.symm.trans ((congrArg R.genusVector hs).trans hgb)) c

lemma allocationGamma_eq_stableGenera (S : CutSkeleton k Q) (R : CutVertexPartition Q u v w)
    (a : BoundedAllocation g n Q)
    (h01 : ∀ i, (a.1 (R.oneVertex i)).val=0)
    (h02 : ∀ i, (a.1 (R.twoVertex i)).val=0) :
    allocationGamma S a = ∏ c : Fin Q,
      Real.Gamma (complexity (R.genusVector (stableGenera R a) c)
        (S.degree c+cutCuspHistogram a.2 c)) := by
  rw [allocationGamma_eq_histogram,stableGenera_recover R a h01 h02]

/-- Reindex a finite selected allocation sum by the stable genus vector and
all individually labelled cusp assignments, retaining an arbitrary selection.
Physical component stability may safely be dropped on the right: every Gamma
has a nonnegative natural argument, including the zero-complexity convention. -/
lemma sum_allocationGamma_le_stableGenera (S : CutSkeleton k Q) (R : CutVertexPartition Q u v w)
    (s : Finset (BoundedAllocation g n Q))
    (h01 : ∀ a ∈ s, ∀ i, (a.1 (R.oneVertex i)).val=0)
    (h02 : ∀ a ∈ s, ∀ i, (a.1 (R.twoVertex i)).val=0)
    (B : (Fin w → ℕ) → (Fin n → Fin Q) → Prop)
    (hB : ∀ a ∈ s, B (stableGenera R a) a.2) :
    (∑ a ∈ s, allocationGamma S a) ≤
      ∑ b ∈ s.image (stableGenera R), ∑ σ : Fin n → Fin Q,
        if B b σ then ∏ c : Fin Q,
          Real.Gamma (complexity (R.genusVector b c) (S.degree c+cutCuspHistogram σ c)) else 0 := by
  let weight : (Fin w → ℕ) × (Fin n → Fin Q) → ℝ := fun b =>
    ∏ c : Fin Q, Real.Gamma (complexity (R.genusVector b.1 c)
      (S.degree c+cutCuspHistogram b.2 c))
  have hinj := stableGenera_cusps_injOn R s h01 h02
  have hsub : s.image (fun a => (stableGenera R a,a.2)) ⊆
      ((s.image (stableGenera R)) ×ˢ univ).filter (fun b => B b.1 b.2) := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_image.mpr ⟨a,ha,rfl⟩,mem_univ _⟩,hB a ha⟩
  have hnonneg (b : (Fin w → ℕ) × (Fin n → Fin Q)) : 0 ≤ weight b :=
    prod_nonneg (fun c _ => Real.Gamma_nonneg_of_nonneg (Nat.cast_nonneg _))
  calc
    _ = ∑ a ∈ s, weight (stableGenera R a,a.2) := by
      apply sum_congr rfl
      intro a ha
      exact allocationGamma_eq_stableGenera S R a (h01 a ha) (h02 a ha)
    _ = ∑ b ∈ s.image (fun a => (stableGenera R a,a.2)),weight b := (sum_image hinj).symm
    _ ≤ ∑ b ∈ ((s.image (stableGenera R)) ×ˢ univ).filter (fun b => B b.1 b.2),weight b :=
      sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => hnonneg b)
    _ = _ := by rw [sum_filter,sum_product]

lemma sum_allocationGamma_le_all_cusps (S : CutSkeleton k Q) (R : CutVertexPartition Q u v w)
    (s : Finset (BoundedAllocation g n Q))
    (h01 : ∀ a ∈ s, ∀ i, (a.1 (R.oneVertex i)).val=0)
    (h02 : ∀ a ∈ s, ∀ i, (a.1 (R.twoVertex i)).val=0) :
    (∑ a ∈ s, allocationGamma S a) ≤
      ∑ b ∈ s.image (stableGenera R), ∑ σ : Fin n → Fin Q,
        ∏ c : Fin Q, Real.Gamma (complexity (R.genusVector b c)
          (S.degree c+cutCuspHistogram σ c)) := by
  simpa only [ite_true] using
    sum_allocationGamma_le_stableGenera S R s h01 h02 (fun _ _ => True) (fun _ _ => trivial)

/-- The image finite genus set automatically satisfies the exact Euler and
stable base budgets needed by the actual local-series coefficient estimate. -/
lemma canonical_stableGenera_spec (S : CutSkeleton k Q) (R : CutVertexPartition Q u v w)
    (A : BoundedAllocation g n Q → Prop)
    (h01 : ∀ a ∈ (canonicalAllocations S g n).filter A, ∀ i, (a.1 (R.oneVertex i)).val=0)
    (h02 : ∀ a ∈ (canonicalAllocations S g n).filter A, ∀ i, (a.1 (R.twoVertex i)).val=0)
    (hstable : ∀ a ∈ (canonicalAllocations S g n).filter A,
      ∀ i, Stable (a.1 (R.stableVertex i)).val (S.degree (R.stableVertex i)))
    (b : Fin w → ℕ)
    (hb : b ∈ ((canonicalAllocations S g n).filter A).image (stableGenera R)) :
    (∀ i, Stable (b i) (S.degree (R.stableVertex i))) ∧
      (∑ c, R.genusVector b c)+k+1=g+Q := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
  refine ⟨hstable a ha,?_⟩
  rw [stableGenera_recover R a (h01 a ha) (h02 a ha)]
  exact ((mem_canonicalAllocations S a).mp (mem_filter.mp ha).1).1

end CutGraphOrbits
end WP.Critical
