import WPFormalization.External.CollarGeometry
import WPFormalization.RandomGeometry.CutBoundaryProduct

/-! A deterministic bound on every actual primitive geodesic below the collar
threshold. Component stability, Euler bookkeeping and the proved boundary-slot
identity give the topological edge bound. The complete short catalog is then
enumerated once and placed in its actual multicurve orbit. No cardinal bound,
integration result or new classical geometric input is assumed. -/
noncomputable section
universe u v w z
open scoped BigOperators
namespace WP.External.MulticurveCutData

/-- The additive form retains the sharp genus-zero bound and avoids truncated
natural subtraction. Connectedness is unnecessary for this consequence. -/
lemma edges_add_three_le {g n r : ℕ} (D : MulticurveCutData n r)
    (hstable : ∀ c, WP.Stable (D.genus c) (D.boundaryCount c))
    (heuler : (∑ c, D.genus c) + r + 1 = g + D.components) :
    r + 3 ≤ 3*g+n := by
  classical
  have hs : 3*D.components ≤ 2*(∑ c, D.genus c)+n+2*r := by
    calc
      3*D.components = ∑ _c : Fin D.components, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ c : Fin D.components, (2*D.genus c+D.boundaryCount c) := by
        apply Finset.sum_le_sum
        intro c _
        have hh := hstable c
        unfold WP.Stable at hh
        omega
      _ = _ := by rw [Finset.sum_add_distrib,←Finset.mul_sum,D.sum_boundaryCount];omega
  omega

lemma edges_le {g n r : ℕ} (D : MulticurveCutData n r)
    (hstable : ∀ c, WP.Stable (D.genus c) (D.boundaryCount c))
    (heuler : (∑ c, D.genus c) + r + 1 = g + D.components) :
    r ≤ 3*g+n-3 := by
  have := D.edges_add_three_le hstable heuler
  omega

end WP.External.MulticurveCutData
namespace WP.External.HyperbolicCurveGeometry
variable {P : WP.PsiTheory} {G : WP.External.WeilPeterssonGeometry.{u,v} P}
    (H : WP.External.HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}
/-- The primitive count is the cardinal of the complete geometric catalog. -/
lemma primitiveCount_eq_card (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    H.primitiveCount X L = (H.shortPrimitive X L).card := by
  classical
  unfold primitiveCount
  let e : {γ : H.Primitive g n X // H.length γ ≤ L} ≃
      {γ : H.Primitive g n X // γ ∈ H.shortPrimitive X L} :=
    Equiv.subtypeEquivRight (fun γ => (H.mem_shortPrimitive X L γ).symm)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]
end WP.External.HyperbolicCurveGeometry

namespace WP.RandomGeometry
open WP.External
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G}
    (T : MulticurveTopology.{u,v,w,z} G H) (C : CollarGeometry G H T) {g n : ℕ}

include C in
/-- All short primitives form one actual disjoint simple multicurve. This
includes empty catalogs and all genera, with no sign restriction on L. -/
lemma shortPrimitive_card_add_three_le (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (X : G.Moduli g n (fun _ => 0)) :
    (H.shortPrimitive X L).card+3 ≤ 3*g+n := by
  classical
  let s := H.shortPrimitive X L
  let e : {γ : H.Primitive g n X // γ ∈ s} ≃ Fin s.card :=
    (Fintype.equivFin _).trans (finCongr (Fintype.card_coe s))
  let γ : Fin s.card → H.Primitive g n X := fun i => (e.symm i).val
  have hi : Function.Injective γ := Subtype.val_injective.comp e.symm.injective
  have hl : ∀ i, H.length (γ i) < 2*Real.arsinh 1 := by
    intro i
    exact ((H.mem_shortPrimitive X L _).1 (e.symm i).property).trans_lt hL
  have hs : ∀ i, H.simple (γ i) := fun i => C.shortPrimitive_simple _ (hl i)
  have hd : ∀ i j, i ≠ j → T.disjoint (γ i) (γ j) := by
    intro i j hij
    exact C.shortSimple_disjoint _ _ (hi.ne hij) (hs i) (hs j) (hl i) (hl j)
  obtain ⟨o,_,_⟩ := T.orbit_partition X γ hi hs hd
  exact (T.cut o).edges_add_three_le (T.cut_stable o) (T.cut_euler o)

include C in
lemma short_primitive_count_add_three_le (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (X : G.Moduli g n (fun _ => 0)) :
    H.primitiveCount X L+3 ≤ 3*g+n := by
  rw [H.primitiveCount_eq_card]
  exact shortPrimitive_card_add_three_le T C L hL X

include C in
lemma short_primitive_count_le (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (X : G.Moduli g n (fun _ => 0)) :
    H.primitiveCount X L ≤ 3*g+n-3 := by
  have := short_primitive_count_add_three_le T C L hL X
  omega

include C in
/-- The traditional typography 3g-3+n is valid in natural arithmetic once
genus is positive. Use the preceding form at genus zero. -/
lemma short_primitive_count_le_of_genus_pos (hg : 1 ≤ g)
    (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (X : G.Moduli g n (fun _ => 0)) :
    H.primitiveCount X L ≤ 3*g-3+n := by
  have := short_primitive_count_add_three_le T C L hL X
  omega

end WP.RandomGeometry
