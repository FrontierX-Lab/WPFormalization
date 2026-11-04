import WPFormalization.External.MulticurveCutData

/-! Finite boundary bookkeeping for an arbitrary labelled cut graph. -/
noncomputable section
set_option maxHeartbeats 0
namespace WP.External.MulticurveCutData
variable {n r : ℕ} (D : MulticurveCutData n r)

/-- Every boundary component is exactly one original cusp or one oriented
side of a cut edge, regardless of the enumerations chosen in each component. -/
def totalBoundaryEquiv : (Σ c, D.Boundary c) ≃ (Fin n ⊕ (Fin r × Fin 2)) where
  toFun p := match p.2 with
    | Sum.inl i => Sum.inl i.val
    | Sum.inr e => Sum.inr e.val
  invFun p := match p with
    | Sum.inl i => ⟨D.cuspVertex i, Sum.inl ⟨i,rfl⟩⟩
    | Sum.inr e => ⟨D.edgeVertex e, Sum.inr ⟨e,rfl⟩⟩
  left_inv p := by
    rcases p with ⟨c, b⟩
    cases b with
    | inl i => rcases i with ⟨i,hi⟩; cases hi; rfl
    | inr e => rcases e with ⟨e,he⟩; cases he; rfl
  right_inv p := by cases p <;> rfl

/-- Each cusp is counted once and each cut edge twice among component
boundaries, including when the two sides belong to the same component. -/
theorem sum_boundaryCount :
    (∑ c : Fin D.components, D.boundaryCount c) = n + 2*r := by
  have h := Fintype.card_congr D.totalBoundaryEquiv
  simpa [Fintype.card_sigma, boundaryCount, Nat.mul_comm] using h

/-- Each physical edge length appears twice; each original cusp contributes
its value at zero. This is valid also for loops and empty cut systems. -/
theorem boundaryLengths_prod {M : Type*} [CommMonoid M] (f : ℝ → M)
    (x : Fin r → ℝ) :
    (∏ c : Fin D.components, ∏ i : Fin (D.boundaryCount c),
      f (D.boundaryLengths x c i)) =
      f 0 ^ n * ∏ e : Fin r, f (x e) ^ 2 := by
  let weight : (Fin n ⊕ (Fin r × Fin 2)) → M := fun b =>
    match b with
    | Sum.inl _ => f 0
    | Sum.inr e => f (x e.1)
  let localWeight : (c : Fin D.components) → D.Boundary c → M := fun _ b =>
    match b with
    | Sum.inl _ => f 0
    | Sum.inr e => f (x e.val.1)
  calc
    _ = ∏ c : Fin D.components, ∏ b : D.Boundary c, localWeight c b := by
      apply Finset.prod_congr rfl
      intro c _
      apply Fintype.prod_equiv (Fintype.equivFin (D.Boundary c)).symm
      intro i
      dsimp only [boundaryLengths, localWeight]
      cases (Fintype.equivFin (D.Boundary c)).symm i <;> rfl
    _ = ∏ p : (Σ c, D.Boundary c), localWeight p.1 p.2 :=
      (Fintype.prod_sigma (fun p : (Σ c, D.Boundary c) => localWeight p.1 p.2)).symm
    _ = ∏ b : (Fin n ⊕ (Fin r × Fin 2)), weight b := by
      apply Fintype.prod_equiv D.totalBoundaryEquiv
      rintro ⟨c,b⟩
      cases b <;> rfl
    _ = _ := by
      rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
      simp [weight, pow_two]

/-- The form used for the hyperbolic boundary factor, whose cusp value is one. -/
theorem boundaryLengths_prod_of_zero_eq_one {M : Type*} [CommMonoid M]
    (f : ℝ → M) (hf : f 0 = 1) (x : Fin r → ℝ) :
    (∏ c : Fin D.components, ∏ i : Fin (D.boundaryCount c),
      f (D.boundaryLengths x c i)) = ∏ e : Fin r, f (x e) ^ 2 := by
  rw [D.boundaryLengths_prod, hf, one_pow, one_mul]

end WP.External.MulticurveCutData
