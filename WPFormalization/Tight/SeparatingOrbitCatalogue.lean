import WPFormalization.Tight.SeparatingOrbitData

/-! A finite catalogue of all labelled cut skeletons and the exact partition
of actual separating tight multicurve orbits into their canonical skeletons.
Loops and both incidences of every edge are retained. -/

noncomputable section
universe u v w z
namespace WP.TightSeparating
open WP.External WP.Critical Finset Set
open scoped BigOperators
instance cutSkeletonFintype (k Q : ℕ) : Fintype (CutSkeleton k Q) :=
  Fintype.ofEquiv (Fin k × Fin 2 → Fin Q)
    { toFun := CutSkeleton.mk
      invFun := CutSkeleton.edgeVertex
      left_inv := fun _ => rfl
      right_inv := fun S => by cases S; rfl }
/-- Finite catalogue depending only on the number of ordered unoriented edges.
It includes loops, every incidence map and every possible vertex count. -/
abbrev SkeletonCatalogue (k : ℕ) := Σ Q : Fin (k+2), CutSkeleton k Q.val
instance (k : ℕ) : Fintype (SkeletonCatalogue k) := by
  unfold SkeletonCatalogue
  infer_instance
lemma skeletonCatalogue_card (k : ℕ) :
    Fintype.card (SkeletonCatalogue k) = ∑ Q : Fin (k+2), Q.val^(2*k) := by
  unfold SkeletonCatalogue
  rw [Fintype.card_sigma]
  apply sum_congr rfl
  intro Q hQ
  rw [Fintype.card_eq.mpr ⟨⟨CutSkeleton.edgeVertex,CutSkeleton.mk,
    (fun S => by cases S; rfl),(fun _ => rfl)⟩⟩]
  simp [Nat.mul_comm]
namespace Orbit
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Qgeom : TightGeodesicGeometry G T H}
  (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
  {g k : ℕ}
local instance : DecidableEq (SkeletonCatalogue k) := Classical.decEq _
abbrev Separating := {o : A.Orbit g 0 k // 2 ≤ (A.cut o).components}
def skeletonKey (o : Separating A (g:=g) (k:=k)) : SkeletonCatalogue k :=
  ⟨⟨(A.cut o.val).components,Nat.lt_succ_of_le
    (CutGraph.components_le (A.cut o.val) (A.cut_connected o.val))⟩,
    ⟨(A.cut o.val).edgeVertex⟩⟩
lemma skeletonKey_vertices (o : Separating A (g:=g) (k:=k)) :
    (skeletonKey A o).1.val = (A.cut o.val).components := rfl
lemma skeletonKey_realizes (o : Separating A (g:=g) (k:=k)) :
    Nonempty ((skeletonKey A o).2.Realization (A.cut o.val)) := by
  refine ⟨⟨Equiv.refl _,fun _ => false,?_⟩⟩
  intro e j
  rfl
def fiberToFixed (K : SkeletonCatalogue k)
    (o : {o : Separating A (g:=g) (k:=k) // skeletonKey A o = K}) : Fixed A K.2 (g:=g) := by
  refine ⟨o.val.val,?_⟩
  have h := skeletonKey_realizes A o.val
  rw [o.property] at h
  exact h
lemma fiberToFixed_injective (K : SkeletonCatalogue k) :
    Function.Injective (fiberToFixed A (g:=g) K) := by
  intro o p he
  apply Subtype.ext
  apply Subtype.ext
  have hh := congrArg Subtype.val he
  exact hh
def fiberFixed (K : SkeletonCatalogue k) : Finset (Fixed A K.2 (g:=g)) := by
  classical
  exact univ.image (fiberToFixed A (g:=g) K)
lemma fiber_sum (K : SkeletonCatalogue k) (x : ℝ) :
    (∑ o : Separating A (g:=g) (k:=k) with skeletonKey A o = K,
      ∏ c, markedF P ((A.cut o.val).genus c) ((A.cut o.val).boundaryCount c) x) =
    ∑ o ∈ fiberFixed A (g:=g) K, ∏ c,
      markedF P ((A.cut o.val).genus c) ((A.cut o.val).boundaryCount c) x := by
  classical
  rw [sum_subtype (p:=fun o : Separating A (g:=g) (k:=k) => skeletonKey A o = K) (univ.filter (fun o : Separating A (g:=g) (k:=k) => skeletonKey A o = K))
    (by simp)]
  unfold fiberFixed
  rw [sum_image (fun o _ p _ he => fiberToFixed_injective A K he)]
  rfl
/-- Exact finite partition of the actual separating orbit sum. -/
lemma sum_partition_by_skeleton (x : ℝ) :
    (∑ o : Separating A (g:=g) (k:=k), ∏ c,
      markedF P ((A.cut o.val).genus c) ((A.cut o.val).boundaryCount c) x) =
    ∑ K : SkeletonCatalogue k, ∑ o ∈ fiberFixed A (g:=g) K, ∏ c,
      markedF P ((A.cut o.val).genus c) ((A.cut o.val).boundaryCount c) x := by
  classical
  simp_rw [←fiber_sum A]
  exact (sum_fiberwise _ (skeletonKey A) _).symm
end Orbit
end WP.TightSeparating
