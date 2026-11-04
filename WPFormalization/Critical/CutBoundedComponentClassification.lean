import WPFormalization.Critical.CutCanonicalPartition
import WPFormalization.Critical.CutPartitionOrbitSummation
/-! A bounded-complexity non-pants component cannot be the unique large
stable vertex of a surviving cut. This is a local consequence of the actual
cut Euler identity, with no recording or expectation assumption. -/
noncomputable section
namespace WP.Critical
open WP.External Finset
open scoped Classical
namespace CutGraphData

lemma single_stable_genus_sum {n k u : ℕ} (D : MulticurveCutData n k)
    (R : CutVertexPartition D.components u 0 1) (hR : CutDataFitsPartition D R) :
    (∑ c, D.genus c) = D.genus (R.stableVertex 0) := by
  have he := R.genusVector_eq_of_leaf_zero D.genus
    (fun i => (hR.1 i).1) (fun i => Fin.elim0 i)
  calc
    _ = ∑ c, R.genusVector (fun i => D.genus (R.stableVertex i)) c :=
      congrArg (fun f : Fin D.components → ℕ => ∑ c, f c) he.symm
    _ = ∑ i : Fin 1, D.genus (R.stableVertex i) := R.genus_sum _
    _ = _ := by simp

lemma single_stable_genus_lower {g n k u : ℕ} (D : MulticurveCutData n k)
    (R : CutVertexPartition D.components u 0 1) (hR : CutDataFitsPartition D R)
    (hEuler : (∑ c, D.genus c) + k + 1 = g + D.components) :
    g ≤ D.genus (R.stableVertex 0) + k := by
  have hs := single_stable_genus_sum D R hR
  have hQ := (R.stableVertex 0).isLt
  rw [hs] at hEuler
  omega

lemma bounded_component_pos_edges {g n k K : ℕ} (D : MulticurveCutData n k)
    (hconn : D.ConnectedWithin univ)
    (hEuler : (∑ c, D.genus c) + k + 1 = g + D.components)
    (hg : k + K + 3 ≤ g) (c : Fin D.components)
    (hK : complexity (D.genus c) (D.boundaryCount c) ≤ K) : 1 ≤ k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  subst k
  have hall (b : Fin D.components) : b = c := by
    have hp := hconn.2 c (mem_univ _) b (mem_univ _)
    induction hp with
    | refl => rfl
    | @tail b d h hbd ih =>
      obtain ⟨_, _, e, _⟩ := hbd
      exact Fin.elim0 e
  have hs : (∑ b, D.genus b) = D.genus c := by
    apply Finset.sum_eq_single c
    · intro b hb hbc
      exact (hbc (hall b)).elim
    · intro hc
      exact (hc (mem_univ c)).elim
  rw [hs] at hEuler
  have hQ := c.isLt
  unfold complexity at hK
  omega

lemma bounded_component_canonical_bad_or_marked {g n k K : ℕ}
    (D : MulticurveCutData n k) (hk : 1 ≤ k)
    (hconn : D.ConnectedWithin univ)
    (hstable : ∀ c, Stable (D.genus c) (D.boundaryCount c))
    (hEuler : (∑ c, D.genus c) + k + 1 = g + D.components)
    (hg : k + K + 3 ≤ g) (c : Fin D.components)
    (hK : complexity (D.genus c) (D.boundaryCount c) ≤ K)
    (hnotPants : ¬(D.genus c = 0 ∧ cuspCount D c = 2 ∧ degree D c = 1)) :
    (baseStableCount D ≠ 1 ∨ twoCount D ≠ 0) ∨
      CutDataHasMarkedPartition D (oneCount D) (twoCount D) (baseStableCount D) := by
  by_cases hb : baseStableCount D ≠ 1 ∨ twoCount D ≠ 0
  · exact Or.inl hb
  have hw : baseStableCount D = 1 := by omega
  have hv : twoCount D = 0 := by omega
  have hpart : CutDataHasPartition D (oneCount D) 0 1 := by
    simpa only [hv, hw] using has_canonicalPartition D hk hconn
  obtain ⟨R, hR⟩ := hpart
  have hroot := single_stable_genus_lower D R hR hEuler
  have hne : c ≠ R.stableVertex 0 := by
    intro he
    rw [he] at hK
    unfold complexity at hK
    omega
  have hc : ∃ i, c = R.oneVertex i := by
    obtain ⟨a, ha⟩ := R.vertices.symm.surjective c
    rcases a with i | (i | i)
    · exact ⟨i, ha.symm⟩
    · exact Fin.elim0 i
    · have hi : i = 0 := Fin.eq_zero i
      subst i
      exact (hne ha.symm).elim
  obtain ⟨i, rfl⟩ := hc
  have hst := hstable (R.oneVertex i)
  have hbdy := boundaryCount_eq D (R.oneVertex i)
  have h01 := hR.1 i
  have hcusps : 3 ≤ cuspCount D (R.oneVertex i) := by
    unfold Stable at hst
    omega
  refine Or.inr ?_
  rw [hv, hw]
  exact ⟨R, i, hR, hcusps⟩

end CutGraphData

universe a b c d
lemma actual_bounded_component_canonical_bad_or_marked {P : PsiTheory}
    {G : WeilPeterssonGeometry.{a,b} P} {H : HyperbolicCurveGeometry.{a,b,c} G}
    (T : MulticurveTopology.{a,b,c,d} G H) {g n k : ℕ} (o : T.Orbit g n k)
    (K : ℝ) (hg : k + Nat.ceil K + 3 ≤ g)
    (c : Fin (T.cut o).components)
    (hK : (complexity ((T.cut o).genus c) ((T.cut o).boundaryCount c) : ℝ) ≤ K)
    (hnotPants : ¬((T.cut o).genus c = 0 ∧ CutGraphData.cuspCount (T.cut o) c = 2 ∧
      CutGraphData.degree (T.cut o) c = 1)) :
    (CutGraphData.baseStableCount (T.cut o) ≠ 1 ∨ CutGraphData.twoCount (T.cut o) ≠ 0) ∨
      CutDataHasMarkedPartition (T.cut o) (CutGraphData.oneCount (T.cut o))
        (CutGraphData.twoCount (T.cut o)) (CutGraphData.baseStableCount (T.cut o)) := by
  have hKNat : complexity ((T.cut o).genus c) ((T.cut o).boundaryCount c) ≤ Nat.ceil K := by
    exact_mod_cast hK.trans (Nat.le_ceil K)
  have hk := CutGraphData.bounded_component_pos_edges (T.cut o)
    (T.cut_connected o) (T.cut_euler o) hg c hKNat
  exact CutGraphData.bounded_component_canonical_bad_or_marked (T.cut o) hk
    (T.cut_connected o) (T.cut_stable o) (T.cut_euler o) hg c hKNat hnotPants

end WP.Critical
