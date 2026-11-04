import WPFormalization.Critical.CutGraphData
import WPFormalization.Critical.CutOrbitEnvelope

/-! Finite reindexing of actual fixed-skeleton multicurve orbits into all
bounded genus and original-cusp-label allocations. Only nonnegative terms
are added. Actual Gamma component weights are transported by cut isomorphism. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.CutGraphOrbits
open WP.External Finset
open scoped Classical

abbrev BoundedAllocation (g n Q : ℕ) :=
  (Fin Q → Fin (g+Q+1)) × (Fin n → Fin Q)

def allocationCutData {g n k Q : ℕ} (S : CutSkeleton k Q)
    (a : BoundedAllocation g n Q) : MulticurveCutData n k :=
  S.cutData (fun c => (a.1 c).val) a.2

/-- Full finite assignments satisfying the actual Euler budget and stability.
Each original cusp is still individually named by Fin n. -/
def canonicalAllocations {k Q : ℕ} (S : CutSkeleton k Q) (g n : ℕ) :
    Finset (BoundedAllocation g n Q) := by
  classical
  exact univ.filter (fun a => (∑ c, (a.1 c).val)+k+1=g+Q ∧
    ∀ c, Stable (a.1 c).val ((allocationCutData S a).boundaryCount c))

lemma mem_canonicalAllocations {g n k Q : ℕ} (S : CutSkeleton k Q)
    (a : BoundedAllocation g n Q) :
    a ∈ canonicalAllocations S g n ↔ (∑ c, (a.1 c).val)+k+1=g+Q ∧
      ∀ c, Stable (a.1 c).val ((allocationCutData S a).boundaryCount c) := by
  classical
  simp only [canonicalAllocations,mem_filter,mem_univ,true_and]

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  (T : MulticurveTopology.{u,v,w,z} G H) {g n k Q : ℕ} (S : CutSkeleton k Q)

def boundedAllocation (o : Orbits T S (g:=g) (n:=n)) : BoundedAllocation g n Q :=
  (fun c => ⟨(allocation T S o).1 c,Nat.lt_succ_of_le (allocation_genus_le T S o c)⟩,
    (allocation T S o).2)

lemma boundedAllocation_injective :
    Function.Injective (boundedAllocation T S (g:=g) (n:=n)) := by
  intro o p he
  apply allocation_injective T S
  apply Prod.ext
  · funext c
    exact congrArg Fin.val (congrArg (fun a : BoundedAllocation g n Q => a.1 c) he)
  · simpa only [boundedAllocation] using congrArg (fun a : BoundedAllocation g n Q => a.2) he

lemma boundedAllocation_cutData (o : Orbits T S (g:=g) (n:=n)) :
    allocationCutData S (boundedAllocation T S o) =
      S.cutData (realization T S o).genus (realization T S o).cusps := rfl

lemma boundedAllocation_mem (o : Orbits T S (g:=g) (n:=n)) :
    boundedAllocation T S o ∈ canonicalAllocations S g n := by
  apply (mem_canonicalAllocations S _).mpr
  refine ⟨allocation_euler T S o,?_⟩
  exact (realization T S o).stable (T.cut_stable o.val)

/-- Exact finite reindexing on the actual orbit image, followed by adding only
nonnegative canonical allocations. Any allocation selection remains explicit. -/
lemma sum_le_canonical (s : Finset (Orbits T S (g:=g) (n:=n)))
    (A : BoundedAllocation g n Q → Prop)
    (hA : ∀ o ∈ s, A (boundedAllocation T S o))
    (weight : BoundedAllocation g n Q → ℝ)
    (hweight : ∀ a ∈ canonicalAllocations S g n, 0 ≤ weight a) :
    (∑ o ∈ s, weight (boundedAllocation T S o)) ≤
      ∑ a ∈ (canonicalAllocations S g n).filter A, weight a := by
  classical
  have hsub : s.image (boundedAllocation T S) ⊆ (canonicalAllocations S g n).filter A := by
    intro a ha
    obtain ⟨o,ho,rfl⟩ := mem_image.mp ha
    exact mem_filter.mpr ⟨boundedAllocation_mem T S o,hA o ho⟩
  calc
    _ = ∑ a ∈ s.image (boundedAllocation T S),weight a :=
      (sum_image (fun o _ p _ he => boundedAllocation_injective T S he)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun a ha _ => hweight a (mem_filter.mp ha).1)

/-- The literal product of actual component Gamma complexities. -/
def allocationGamma {g n k Q : ℕ} (S : CutSkeleton k Q)
    (a : BoundedAllocation g n Q) : ℝ :=
  ∏ c : Fin Q, Real.Gamma (complexity (a.1 c).val ((allocationCutData S a).boundaryCount c))

lemma allocationGamma_nonneg {g n k Q : ℕ} (S : CutSkeleton k Q)
    (a : BoundedAllocation g n Q) (ha : a ∈ canonicalAllocations S g n) :
    0 ≤ allocationGamma S a := by
  apply prod_nonneg
  intro c hc
  apply (Real.Gamma_pos_of_pos _).le
  have hs := ((mem_canonicalAllocations S a).mp ha).2 c
  have hn : 0 < complexity (a.1 c).val ((allocationCutData S a).boundaryCount c) := by
    unfold Stable complexity at *
    omega
  exact_mod_cast hn

lemma actualGamma_eq (o : Orbits T S (g:=g) (n:=n)) :
    (∏ c : Fin (T.cut o.val).components,
      Real.Gamma (complexity ((T.cut o.val).genus c) ((T.cut o.val).boundaryCount c))) =
      allocationGamma S (boundedAllocation T S o) := by
  let R := realization T S o
  have he (c : Fin (T.cut o.val).components) :
      complexity ((T.cut o.val).genus c) ((T.cut o.val).boundaryCount c) =
        complexity ((allocation T S o).1 (R.vertices c))
          ((allocationCutData S (boundedAllocation T S o)).boundaryCount (R.vertices c)) := by
    rw [R.isomorphism.boundaryCount_eq c]
    change complexity ((T.cut o.val).genus c) _ = complexity (R.genus (R.vertices c)) _
    rw [CutSkeleton.Realization.genus,R.vertices.symm_apply_apply]
    rfl
  simp_rw [he]
  simpa only [allocationGamma,boundedAllocation] using
    Equiv.prod_comp R.vertices (fun c =>
      Real.Gamma (complexity ((allocation T S o).1 c)
        ((allocationCutData S (boundedAllocation T S o)).boundaryCount c)))

lemma sum_actualGamma_le_canonical (s : Finset (Orbits T S (g:=g) (n:=n)))
    (A : BoundedAllocation g n Q → Prop)
    (hA : ∀ o ∈ s, A (boundedAllocation T S o)) :
    (∑ o ∈ s, ∏ c : Fin (T.cut o.val).components,
      Real.Gamma (complexity ((T.cut o.val).genus c) ((T.cut o.val).boundaryCount c))) ≤
      ∑ a ∈ (canonicalAllocations S g n).filter A, allocationGamma S a := by
  simp_rw [actualGamma_eq T S]
  exact sum_le_canonical T S s A hA (allocationGamma S) (allocationGamma_nonneg S)

end WP.Critical.CutGraphOrbits

namespace WP.Critical.CutGraphOrbits
open WP.External Finset MeasureTheory
open scoped Classical ENNReal

/-- Actual Mirzakhani orbit expectations over any finite selection of one
skeleton are bounded by the complete admissible genus/cusp-label Gamma sum.
The selection is retained as a literal predicate on canonical assignments. -/
lemma sum_orbit_expectation_gamma_envelope {P : PsiTheory}
    (G : WeilPeterssonGeometry.{u,v} P) {H : HyperbolicCurveGeometry.{u,v,w} G}
    (T : MulticurveTopology.{u,v,w,z} G H) (MI : MirzakhaniIntegration G H T)
    (k Q : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n:ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q,
      ∀ s : Finset (Orbits T S (g:=g) (n:=n)),
      ∀ B : BoundedAllocation g n Q → Prop,
      (∀ o ∈ s, B (boundedAllocation T S o)) →
      (∑ o ∈ s, ∫⁻ X, T.orbitSum o.val (cutLengthTest k L) X ∂wpProbability G g n) ≤
        ENNReal.ofReal (C*(∑ a ∈ (canonicalAllocations S g n).filter B, allocationGamma S a)/
          Real.Gamma (complexity g n)) := by
  obtain ⟨C,hC,G₁,hbound⟩ := cut_orbit_expectation_gamma_envelope G T MI k Q hk hQ A L hA hL
  refine ⟨C,hC,max G₁ 3,?_⟩
  intro g hg n hn hcritical S s B hB
  have hΓpos : 0 < Real.Gamma (complexity g n) := by
    apply Real.Gamma_pos_of_pos
    have hh : 0 < complexity g n := by unfold complexity;omega
    exact_mod_cast hh
  have hΓ (o : Orbits T S (g:=g) (n:=n)) :
      0 ≤ ∏ c : Fin (T.cut o.val).components,
        Real.Gamma (complexity ((T.cut o.val).genus c) ((T.cut o.val).boundaryCount c)) := by
    rw [actualGamma_eq T S o]
    exact allocationGamma_nonneg S _ (boundedAllocation_mem T S o)
  have hsum := mul_le_mul_of_nonneg_left (sum_actualGamma_le_canonical T S s B hB)
    (div_nonneg hC.le hΓpos.le)
  calc
    _ ≤ ∑ o ∈ s, ENNReal.ofReal (C*(∏ c : Fin (T.cut o.val).components,
        Real.Gamma (complexity ((T.cut o.val).genus c) ((T.cut o.val).boundaryCount c)))/
          Real.Gamma (complexity g n)) := by
      apply sum_le_sum
      intro o ho
      apply hbound g (by omega) n hn hcritical o.val
      simpa only [Fintype.card_fin] using Fintype.card_congr (realization T S o).vertices
    _ = ENNReal.ofReal ((C/Real.Gamma (complexity g n))*
        (∑ o ∈ s, ∏ c : Fin (T.cut o.val).components,
          Real.Gamma (complexity ((T.cut o.val).genus c) ((T.cut o.val).boundaryCount c)))) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun o _ => div_nonneg (mul_nonneg hC.le (hΓ o)) hΓpos.le)]
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro o ho
      ring
    _ ≤ ENNReal.ofReal ((C/Real.Gamma (complexity g n))*
        (∑ a ∈ (canonicalAllocations S g n).filter B, allocationGamma S a)) :=
      ENNReal.ofReal_le_ofReal hsum
    _ = _ := congrArg ENNReal.ofReal (by ring)
end WP.Critical.CutGraphOrbits
