import Mathlib
noncomputable section
namespace WP.External
structure MulticurveCutData (n r : ℕ) where
  components : ℕ
  genus : Fin components → ℕ
  cuspVertex : Fin n → Fin components
  edgeVertex : Fin r × Fin 2 → Fin components
namespace MulticurveCutData
variable {n r : ℕ} (D : MulticurveCutData n r)
def cuspSet (U : Finset (Fin D.components)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => D.cuspVertex i ∈ U)
def internalEdges (U : Finset (Fin D.components)) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun e => D.edgeVertex (e,0) ∈ U ∧ D.edgeVertex (e,1) ∈ U)
def crossingEdges (U : Finset (Fin D.components)) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun e => Xor (D.edgeVertex (e,0) ∈ U) (D.edgeVertex (e,1) ∈ U))
def AdjacentWithin (U : Finset (Fin D.components)) (a b : Fin D.components) : Prop :=
  a ∈ U ∧ b ∈ U ∧ ∃ e : Fin r,
    (D.edgeVertex (e,0) = a ∧ D.edgeVertex (e,1) = b) ∨
    (D.edgeVertex (e,1) = a ∧ D.edgeVertex (e,0) = b)
def ConnectedWithin (U : Finset (Fin D.components)) : Prop :=
  U.Nonempty ∧ ∀ a ∈ U, ∀ b ∈ U, Relation.ReflTransGen (D.AdjacentWithin U) a b
def IsSide (e : Fin r) (U : Finset (Fin D.components)) : Prop :=
  U.Nonempty ∧ (Finset.univ \ U).Nonempty ∧
  D.crossingEdges U = {e} ∧ D.ConnectedWithin U ∧ D.ConnectedWithin (Finset.univ \ U)
def SideGenus (U : Finset (Fin D.components)) (j : ℕ) : Prop :=
  (∑ c ∈ U, D.genus c) + (D.internalEdges U).card + 1 = U.card + j
def PlanarSide (e : Fin r) (S : Finset (Fin n)) : Prop :=
  ∃ U : Finset (Fin D.components), D.IsSide e U ∧ D.SideGenus U 0 ∧ D.cuspSet U = S
def HasOneHandleSide (e : Fin r) : Prop :=
  ∃ U : Finset (Fin D.components), D.IsSide e U ∧ D.SideGenus U 1 ∧ D.cuspSet U = ∅
def oneHandleCount : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => D.HasOneHandleSide e)).card

def FlipPreserves (b : Fin r → Bool) : Prop :=
  ∃ v : Equiv.Perm (Fin D.components),
    (∀ c, D.genus (v c) = D.genus c) ∧
    (∀ i, v (D.cuspVertex i) = D.cuspVertex i) ∧
    (∀ e j, v (D.edgeVertex (e, j)) = D.edgeVertex (e, if b e then j.rev else j))
def orientationStabilizerIndex : ℕ := Nat.card {b : Fin r → Bool // D.FlipPreserves b}
lemma orientationStabilizerIndex_pos : 0 < D.orientationStabilizerIndex := by
  classical
  unfold orientationStabilizerIndex
  have h : D.FlipPreserves (fun _ => false) := by
    refine ⟨Equiv.refl _, ?_, ?_, ?_⟩ <;> simp
  letI : Nonempty {b : Fin r → Bool // D.FlipPreserves b} := ⟨⟨_,h⟩⟩
  exact Nat.card_pos


def Boundary (c : Fin D.components) :=
  {i : Fin n // D.cuspVertex i = c} ⊕ {e : Fin r × Fin 2 // D.edgeVertex e = c}

instance (c : Fin D.components) : Fintype (D.Boundary c) := by
  classical
  unfold Boundary
  infer_instance

def boundaryCount (c : Fin D.components) : ℕ := Fintype.card (D.Boundary c)

/-- The original cusp lengths are zero. Every cut edge supplies its physical
length once on each of its two incident sides, including loops. -/
def boundaryLengths (x : Fin r → ℝ) (c : Fin D.components) :
    Fin (D.boundaryCount c) → ℝ := fun i =>
  match (Fintype.equivFin (D.Boundary c)).symm i with
  | Sum.inl _ => 0
  | Sum.inr e => x e.val.1


structure Isomorphism {n r : ℕ} (D E : MulticurveCutData n r) where
  vertexEquiv : Fin D.components ≃ Fin E.components
  flip : Fin r → Bool
  genus_eq : ∀ c, E.genus (vertexEquiv c) = D.genus c
  cusp_eq : ∀ i, vertexEquiv (D.cuspVertex i) = E.cuspVertex i
  edge_eq : ∀ e j, vertexEquiv (D.edgeVertex (e,j)) =
    E.edgeVertex (e, if flip e then j.rev else j)

end MulticurveCutData
end WP.External
