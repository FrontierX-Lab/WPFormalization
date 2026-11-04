import WPFormalization.External.MulticurveCutData

/-! The local stable-graph argument excluding nested two-cusp pants. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External

lemma cut_boundary_incidence_sum {n r : ℕ} (D : MulticurveCutData n r)
    (U : Finset (Fin D.components)) :
    (∑ c ∈ U, D.boundaryCount c) =
      (D.cuspSet U).card + 2*(D.internalEdges U).card + (D.crossingEdges U).card := by
  classical
  have h0 : (∑ c ∈ U, Fintype.card {i : Fin n // D.cuspVertex i = c}) =
      (D.cuspSet U).card := by
    simp only [Fintype.card_subtype, MulticurveCutData.cuspSet]
    exact Finset.sum_card_fiberwise_eq_card_filter Finset.univ U D.cuspVertex
  have h1 : (∑ c ∈ U, Fintype.card {e : Fin r × Fin 2 // D.edgeVertex e = c}) =
      (Finset.univ.filter (fun e : Fin r × Fin 2 => D.edgeVertex e ∈ U)).card := by
    simp only [Fintype.card_subtype]
    exact Finset.sum_card_fiberwise_eq_card_filter Finset.univ U D.edgeVertex
  have h2 : (Finset.univ.filter (fun e : Fin r × Fin 2 => D.edgeVertex e ∈ U)).card =
      2*(D.internalEdges U).card + (D.crossingEdges U).card := by
    simp only [Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_two,
      MulticurveCutData.internalEdges, MulticurveCutData.crossingEdges]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases h0 : D.edgeVertex (e,0) ∈ U <;>
      by_cases h1 : D.edgeVertex (e,1) ∈ U <;> simp [h0,h1]
  calc
    _ = (∑ c ∈ U, Fintype.card {i : Fin n // D.cuspVertex i = c}) +
        ∑ c ∈ U, Fintype.card {e : Fin r × Fin 2 // D.edgeVertex e = c} := by
      simp only [MulticurveCutData.boundaryCount, MulticurveCutData.Boundary,
        Fintype.card_sum, Finset.sum_add_distrib]
    _ = _ := by rw [h0,h1,h2]; omega

/-- A planar side with two original cusps has exactly one component after all
other disjoint simple curves are cut. Every component is stable, so its Euler
characteristic costs at least one; the whole side has cost exactly one. -/
lemma planar_two_cusp_side_single {n r : ℕ} (D : MulticurveCutData n r)
    (hstable : ∀ c, 2 < 2*D.genus c + D.boundaryCount c)
    (e : Fin r) (U : Finset (Fin D.components))
    (hside : D.IsSide e U) (hgenus : D.SideGenus U 0)
    (hcusps : (D.cuspSet U).card = 2) : U.card = 1 := by
  classical
  have hbound : 3*U.card ≤ 2*(∑ c ∈ U, D.genus c) + ∑ c ∈ U, D.boundaryCount c := by
    calc
      _ = ∑ _c ∈ U, 3 := by simp [mul_comm]
      _ ≤ ∑ c ∈ U, (2*D.genus c + D.boundaryCount c) := by
        exact Finset.sum_le_sum (fun c _ => hstable c)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hinc := cut_boundary_incidence_sum D U
  have hcross : (D.crossingEdges U).card = 1 := by rw [hside.2.2.1]; simp
  have hpos := Finset.card_pos.mpr hside.1
  change (∑ c ∈ U, D.genus c) + (D.internalEdges U).card + 1 = U.card + 0 at hgenus
  omega


/-- A completely explicit pants leaf, recovered from generic cut incidence. -/
structure PantsLeafData {n r : ℕ} (D : MulticurveCutData n r) (e : Fin r)
    (c : Fin D.components) : Prop where
  genus_zero : D.genus c = 0
  two_cusps : (D.cuspSet {c}).card = 2
  no_internal : D.internalEdges {c} = ∅
  crossing : D.crossingEdges {c} = {e}

lemma planar_two_cusp_leaf {n r : ℕ} (D : MulticurveCutData n r)
    (hstable : ∀ c, 2 < 2*D.genus c + D.boundaryCount c)
    (e : Fin r) (S : Finset (Fin n)) (hplanar : D.PlanarSide e S) (hS : S.card = 2) :
    ∃ c : Fin D.components, PantsLeafData D e c := by
  classical
  rcases hplanar with ⟨U, hside, hgenus, hcusp⟩
  have hcu : (D.cuspSet U).card = 2 := by rw [hcusp,hS]
  have hsingle := planar_two_cusp_side_single D hstable e U hside hgenus hcu
  rcases Finset.card_eq_one.mp hsingle with ⟨c,hc⟩
  subst U
  have he : D.genus c + (D.internalEdges {c}).card = 0 := by
    have hg := hgenus
    simp only [MulticurveCutData.SideGenus, Finset.sum_singleton, Finset.card_singleton] at hg
    omega
  refine ⟨c, (by omega), hcu, ?_, hside.2.2.1⟩
  exact Finset.card_eq_zero.mp (by omega)

lemma planar_two_cusp_leaf_labels {n r : ℕ} (D : MulticurveCutData n r)
    (hstable : ∀c, 2 < 2*D.genus c + D.boundaryCount c)
    (e : Fin r) (S : Finset (Fin n)) (hplanar : D.PlanarSide e S) (hS : S.card = 2) :
    ∃c : Fin D.components, PantsLeafData D e c ∧ D.cuspSet {c} = S := by
  classical
  rcases hplanar with ⟨U,hs,hg,hc⟩
  have hu := planar_two_cusp_side_single D hstable e U hs hg (hc ▸ hS)
  rcases Finset.card_eq_one.mp hu with ⟨c,hcU⟩
  subst U
  have hz : D.genus c + (D.internalEdges {c}).card = 0 := by
    have h := hg
    simp only [MulticurveCutData.SideGenus, Finset.sum_singleton, Finset.card_singleton] at h
    omega
  refine ⟨c,⟨by omega, hc ▸ hS, Finset.card_eq_zero.mp (by omega),hs.2.2.1⟩,hc⟩

lemma pantsLeaf_injective {n r : ℕ} (D : MulticurveCutData n r)
    (leaf : Fin r → Fin D.components) (hleaf : ∀ e, PantsLeafData D e (leaf e)) :
    Function.Injective leaf := by
  intro i j hij
  have he := (hleaf i).crossing
  rw [hij, (hleaf j).crossing] at he
  simpa only [Finset.singleton_inj] using he.symm

lemma pantsLeaf_edge_iff {n r : ℕ} (D : MulticurveCutData n r)
    (e : Fin r) (c : Fin D.components) (h : PantsLeafData D e c) (j : Fin r) :
    (D.edgeVertex (j,0) = c ∨ D.edgeVertex (j,1) = c) ↔ j = e := by
  classical
  have hn : ¬ (D.edgeVertex (j,0) = c ∧ D.edgeVertex (j,1) = c) := by
    have hm : j ∉ D.internalEdges {c} := by rw [h.no_internal]; simp
    simpa only [MulticurveCutData.internalEdges, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton] using hm
  have hx : Xor (D.edgeVertex (j,0) = c) (D.edgeVertex (j,1) = c) ↔ j = e := by
    have hm : j ∈ D.crossingEdges {c} ↔ j = e := by rw [h.crossing]; simp
    simpa only [MulticurveCutData.crossingEdges, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton] using hm
  rw [← hx]
  unfold Xor
  tauto

lemma pantsLeaf_boundaryCount {n r : ℕ} (D : MulticurveCutData n r)
    (e : Fin r) (c : Fin D.components) (h : PantsLeafData D e c) :
    D.boundaryCount c = 3 := by
  have hc := cut_boundary_incidence_sum D {c}
  simpa only [Finset.sum_singleton, h.two_cusps, h.no_internal, h.crossing,
    Finset.card_empty, Finset.card_singleton] using hc

end WP.RandomGeometry
