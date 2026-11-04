import WPFormalization.External.MulticurveCutData

noncomputable section
namespace WP.External.MulticurveCutData
namespace Isomorphism
variable {n r : ℕ} {D E F : MulticurveCutData n r}

/-- Relabel vertices while keeping all labelled edges and cusps. -/
def refl (D : MulticurveCutData n r) : D.Isomorphism D where
  vertexEquiv := Equiv.refl _
  flip := fun _ => false
  genus_eq := by simp
  cusp_eq := by simp
  edge_eq := by simp

/-- Reversing an isomorphism reverses exactly the same edge orientations. -/
def symm (f : D.Isomorphism E) : E.Isomorphism D where
  vertexEquiv := f.vertexEquiv.symm
  flip := f.flip
  genus_eq c := by simpa using (f.genus_eq (f.vertexEquiv.symm c)).symm
  cusp_eq i := by simpa using congrArg f.vertexEquiv.symm (f.cusp_eq i).symm
  edge_eq e j := by
    apply f.vertexEquiv.injective
    cases h : f.flip e <;> simpa [h] using (f.edge_eq e (if f.flip e then j.rev else j)).symm

/-- Composition uses the parity of the two reversals on each labelled edge. -/
def trans (f : D.Isomorphism E) (q : E.Isomorphism F) : D.Isomorphism F where
  vertexEquiv := f.vertexEquiv.trans q.vertexEquiv
  flip := fun e => f.flip e ^^ q.flip e
  genus_eq c := (q.genus_eq (f.vertexEquiv c)).trans (f.genus_eq c)
  cusp_eq i := by simp only [Equiv.trans_apply, f.cusp_eq, q.cusp_eq]
  edge_eq e j := by
    simp only [Equiv.trans_apply, f.edge_eq, q.edge_eq]
    cases f.flip e <;> cases q.flip e <;> simp

/-- The induced bijection of oriented half edges preserves each physical edge. -/
def halfEdgeEquiv (f : D.Isomorphism E) : (Fin r × Fin 2) ≃ (Fin r × Fin 2) where
  toFun p := (p.1, if f.flip p.1 then p.2.rev else p.2)
  invFun p := (p.1, if f.flip p.1 then p.2.rev else p.2)
  left_inv p := by cases h : f.flip p.1 <;> simp [h]
  right_inv p := by cases h : f.flip p.1 <;> simp [h]

@[simp] theorem halfEdgeEquiv_fst (f : D.Isomorphism E) (p : Fin r × Fin 2) :
    (f.halfEdgeEquiv p).1 = p.1 := rfl

@[simp] theorem halfEdgeEquiv_incidence (f : D.Isomorphism E) (p : Fin r × Fin 2) :
    E.edgeVertex (f.halfEdgeEquiv p) = f.vertexEquiv (D.edgeVertex p) :=
  (f.edge_eq p.1 p.2).symm

/-- Transport of the actual boundary components, retaining cusp and edge labels. -/
def boundaryEquiv (f : D.Isomorphism E) (c : Fin D.components) :
    D.Boundary c ≃ E.Boundary (f.vertexEquiv c) :=
  Equiv.sumCongr
    ((Equiv.refl (Fin n)).subtypeEquiv (by
      intro i
      change D.cuspVertex i = c ↔ E.cuspVertex i = f.vertexEquiv c
      rw [← f.cusp_eq i]
      exact f.vertexEquiv.injective.eq_iff.symm))
    (f.halfEdgeEquiv.subtypeEquiv (by
      intro p
      rw [f.halfEdgeEquiv_incidence]
      exact f.vertexEquiv.injective.eq_iff.symm))

theorem boundaryCount_eq (f : D.Isomorphism E) (c : Fin D.components) :
    D.boundaryCount c = E.boundaryCount (f.vertexEquiv c) :=
  Fintype.card_congr (f.boundaryEquiv c)

/-- The boundary indices are arbitrary finite enumerations; this is their
actual reindexing induced by a cut isomorphism. -/
def boundaryIndexEquiv (f : D.Isomorphism E) (c : Fin D.components) :
    Fin (D.boundaryCount c) ≃ Fin (E.boundaryCount (f.vertexEquiv c)) :=
  (Fintype.equivFin (D.Boundary c)).symm.trans
    ((f.boundaryEquiv c).trans (Fintype.equivFin (E.Boundary (f.vertexEquiv c))))

theorem boundaryLengths_reindex (f : D.Isomorphism E) (x : Fin r → ℝ)
    (c : Fin D.components) :
    E.boundaryLengths x (f.vertexEquiv c) ∘ f.boundaryIndexEquiv c =
      D.boundaryLengths x c := by
  funext i
  have hi : (Fintype.equivFin (E.Boundary (f.vertexEquiv c))).symm
      (f.boundaryIndexEquiv c i) =
      f.boundaryEquiv c ((Fintype.equivFin (D.Boundary c)).symm i) := by
    exact (Fintype.equivFin (E.Boundary (f.vertexEquiv c))).symm_apply_apply _
  simp only [Function.comp_apply, boundaryLengths, hi]
  generalize (Fintype.equivFin (D.Boundary c)).symm i = b
  cases b with
  | inl b => rfl
  | inr b => rfl

/-- Vertex subsets are transported by the vertex bijection. -/
def vertices (f : D.Isomorphism E) (U : Finset (Fin D.components)) :
    Finset (Fin E.components) := U.map f.vertexEquiv.toEmbedding

@[simp] theorem mem_vertices (f : D.Isomorphism E) (U : Finset (Fin D.components))
    (c : Fin D.components) : f.vertexEquiv c ∈ f.vertices U ↔ c ∈ U := by
  simp [vertices]

@[simp] theorem symm_vertices (f : D.Isomorphism E) (U : Finset (Fin D.components)) :
    f.symm.vertices (f.vertices U) = U := by
  ext c
  simp [vertices, symm, Finset.mem_map_equiv]

@[simp] theorem vertices_compl (f : D.Isomorphism E) (U : Finset (Fin D.components)) :
    f.vertices (Finset.univ \ U) = Finset.univ \ f.vertices U := by
  ext c
  simp [vertices, Finset.mem_map_equiv]

@[simp] theorem cuspSet_vertices (f : D.Isomorphism E) (U : Finset (Fin D.components)) :
    E.cuspSet (f.vertices U) = D.cuspSet U := by
  ext i
  simp only [cuspSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← f.cusp_eq i, f.mem_vertices]

@[simp] theorem internalEdges_vertices (f : D.Isomorphism E)
    (U : Finset (Fin D.components)) : E.internalEdges (f.vertices U) = D.internalEdges U := by
  ext e
  have h0 := f.edge_eq e 0
  have h1 := f.edge_eq e 1
  cases h : f.flip e <;> simp only [h, Bool.false_eq_true, ite_false, ite_true] at h0 h1
  · simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← h0, ← h1, f.mem_vertices, f.mem_vertices]
  · change _ = E.edgeVertex (e,1) at h0
    change _ = E.edgeVertex (e,0) at h1
    simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← h0, ← h1, f.mem_vertices, f.mem_vertices, and_comm]

@[simp] theorem crossingEdges_vertices (f : D.Isomorphism E)
    (U : Finset (Fin D.components)) : E.crossingEdges (f.vertices U) = D.crossingEdges U := by
  ext e
  have h0 := f.edge_eq e 0
  have h1 := f.edge_eq e 1
  cases h : f.flip e <;> simp only [h, Bool.false_eq_true, ite_false, ite_true] at h0 h1
  · simp only [crossingEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← h0, ← h1, f.mem_vertices, f.mem_vertices]
  · change _ = E.edgeVertex (e,1) at h0
    change _ = E.edgeVertex (e,0) at h1
    simp only [crossingEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← h0, ← h1, f.mem_vertices, f.mem_vertices, xor_comm]

theorem adjacentWithin (f : D.Isomorphism E) (U : Finset (Fin D.components))
    {a b : Fin D.components} (hab : D.AdjacentWithin U a b) :
    E.AdjacentWithin (f.vertices U) (f.vertexEquiv a) (f.vertexEquiv b) := by
  rcases hab with ⟨ha,hb,e,he⟩
  refine ⟨(f.mem_vertices U a).2 ha, (f.mem_vertices U b).2 hb, e, ?_⟩
  have h0 := f.edge_eq e 0
  have h1 := f.edge_eq e 1
  cases h : f.flip e <;> simp only [h, Bool.false_eq_true, ite_false, ite_true] at h0 h1
  · rcases he with ⟨hA,hB⟩ | ⟨hA,hB⟩
    · exact Or.inl ⟨h0.symm.trans (congrArg _ hA), h1.symm.trans (congrArg _ hB)⟩
    · exact Or.inr ⟨h1.symm.trans (congrArg _ hA), h0.symm.trans (congrArg _ hB)⟩
  · have hr0 : (0 : Fin 2).rev = 1 := rfl
    have hr1 : (1 : Fin 2).rev = 0 := rfl
    rw [hr0] at h0
    rw [hr1] at h1
    rcases he with ⟨hA,hB⟩ | ⟨hA,hB⟩
    · exact Or.inr ⟨h0.symm.trans (congrArg _ hA), h1.symm.trans (congrArg _ hB)⟩
    · exact Or.inl ⟨h1.symm.trans (congrArg _ hA), h0.symm.trans (congrArg _ hB)⟩

theorem connectedWithin (f : D.Isomorphism E) (U : Finset (Fin D.components))
    (hU : D.ConnectedWithin U) : E.ConnectedWithin (f.vertices U) := by
  constructor
  · rcases hU.1 with ⟨c,hc⟩
    exact ⟨f.vertexEquiv c, (f.mem_vertices U c).2 hc⟩
  · intro a ha b hb
    have ha' : f.vertexEquiv.symm a ∈ U := by simpa [vertices, Finset.mem_map_equiv] using ha
    have hb' : f.vertexEquiv.symm b ∈ U := by simpa [vertices, Finset.mem_map_equiv] using hb
    have hh := hU.2 _ ha' _ hb'
    have lift : ∀ {c d}, Relation.ReflTransGen (D.AdjacentWithin U) c d →
        Relation.ReflTransGen (E.AdjacentWithin (f.vertices U)) (f.vertexEquiv c) (f.vertexEquiv d) := by
      intro c d h
      induction h with
      | refl => exact .refl
      | tail h hstep ih => exact ih.tail (f.adjacentWithin U hstep)
    simpa using lift hh

theorem isSide (f : D.Isomorphism E) (U : Finset (Fin D.components)) (e : Fin r)
    (hU : D.IsSide e U) : E.IsSide e (f.vertices U) := by
  rcases hU with ⟨hn,hcn,hcross,hconn,hcconn⟩
  have hn' := (f.connectedWithin U hconn).1
  have hcconn' := f.connectedWithin (Finset.univ \ U) hcconn
  rw [f.vertices_compl] at hcconn'
  exact ⟨hn', hcconn'.1, by simpa using hcross, f.connectedWithin U hconn, hcconn'⟩

theorem sideGenus (f : D.Isomorphism E) (U : Finset (Fin D.components)) (j : ℕ)
    (hU : D.SideGenus U j) : E.SideGenus (f.vertices U) j := by
  unfold SideGenus at hU ⊢
  rw [f.internalEdges_vertices]
  simpa only [vertices, Finset.sum_map, Equiv.toEmbedding_apply,
    f.genus_eq, Finset.card_map] using hU

theorem hasOneHandleSide (f : D.Isomorphism E) (e : Fin r) :
    D.HasOneHandleSide e ↔ E.HasOneHandleSide e := by
  constructor
  · rintro ⟨U,hside,hgen,hcusp⟩
    exact ⟨f.vertices U, f.isSide U e hside, f.sideGenus U 1 hgen, by simpa using hcusp⟩
  · rintro ⟨U,hside,hgen,hcusp⟩
    exact ⟨f.symm.vertices U, f.symm.isSide U e hside, f.symm.sideGenus U 1 hgen, by simpa using hcusp⟩

/-- The same labelled cusp subset bounds a planar side before and after
transport. This also handles zero-edge and loop configurations unchanged. -/
theorem planarSide (f : D.Isomorphism E) (e : Fin r) (S : Finset (Fin n)) :
    D.PlanarSide e S ↔ E.PlanarSide e S := by
  constructor
  · rintro ⟨U,hside,hgen,hcusp⟩
    exact ⟨f.vertices U, f.isSide U e hside, f.sideGenus U 0 hgen, by simpa using hcusp⟩
  · rintro ⟨U,hside,hgen,hcusp⟩
    exact ⟨f.symm.vertices U, f.symm.isSide U e hside, f.symm.sideGenus U 0 hgen, by simpa using hcusp⟩

theorem oneHandleCount_eq (f : D.Isomorphism E) : D.oneHandleCount = E.oneHandleCount := by
  classical
  unfold oneHandleCount
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, f.hasOneHandleSide]

/-- Conjugation transports precisely the same allowed edge reversals. -/
theorem flipPreserves (f : D.Isomorphism E) (b : Fin r → Bool) :
    D.FlipPreserves b → E.FlipPreserves b := by
  rintro ⟨v,hgen,hcusp,hedge⟩
  let q : D.Isomorphism D := ⟨v,b,hgen,hcusp,hedge⟩
  let t := f.symm.trans (q.trans f)
  refine ⟨t.vertexEquiv, t.genus_eq, t.cusp_eq, ?_⟩
  intro e j
  have h := t.edge_eq e j
  have hf : t.flip e = b e := by
    change (f.flip e ^^ (b e ^^ f.flip e)) = b e
    cases f.flip e <;> cases b e <;> rfl
  simpa only [hf] using h

theorem flipPreserves_iff (f : D.Isomorphism E) (b : Fin r → Bool) :
    D.FlipPreserves b ↔ E.FlipPreserves b :=
  ⟨f.flipPreserves b, f.symm.flipPreserves b⟩

theorem orientationStabilizerIndex_eq (f : D.Isomorphism E) :
    D.orientationStabilizerIndex = E.orientationStabilizerIndex := by
  unfold orientationStabilizerIndex
  exact Nat.card_congr ((Equiv.refl (Fin r → Bool)).subtypeEquiv (f.flipPreserves_iff))

end Isomorphism
end WP.External.MulticurveCutData
