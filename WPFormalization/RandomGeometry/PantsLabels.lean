import Mathlib
noncomputable section
namespace WP.RandomGeometry

/-- Ordered slots contain unordered disjoint pairs of labeled cusps. -/
def PantsLabels (n r : ℕ) :=
  {f : (Fin r × Fin 2) ↪ Fin n // ∀ i, f (i, 0) < f (i, 1)}

instance (n r : ℕ) : Fintype (PantsLabels n r) := inferInstanceAs
  (Fintype {f : (Fin r × Fin 2) ↪ Fin n // ∀ i, f (i, 0) < f (i, 1)})

def pairFlip {r : ℕ} (b : Fin r → Bool) : (Fin r × Fin 2) ≃ (Fin r × Fin 2) where
  toFun p := (p.1, if b p.1 then p.2.rev else p.2)
  invFun p := (p.1, if b p.1 then p.2.rev else p.2)
  left_inv p := by cases h : b p.1 <;> simp [h]
  right_inv p := by cases h : b p.1 <;> simp [h]

lemma pairFlip_self {r : ℕ} (b : Fin r → Bool) (p : Fin r × Fin 2) :
    pairFlip b (pairFlip b p) = p := (pairFlip b).left_inv p

def pairOrientation {n r : ℕ} (f : (Fin r × Fin 2) ↪ Fin n) : Fin r → Bool :=
  fun i => decide (f (i, 1) < f (i, 0))

def sortPairEmbedding {n r : ℕ} (f : (Fin r × Fin 2) ↪ Fin n) : PantsLabels n r :=
  ⟨(pairFlip (pairOrientation f)).toEmbedding.trans f, by
    intro i
    have hne : f (i, 0) ≠ f (i, 1) := by
      intro he
      have := f.injective he
      exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd this)
    change f (i, if decide (f (i, 1) < f (i, 0)) then (0 : Fin 2).rev else 0) <
      f (i, if decide (f (i, 1) < f (i, 0)) then (1 : Fin 2).rev else 1)
    by_cases h : f (i, 1) < f (i, 0)
    · simpa [h] using h
    · simpa [h] using lt_of_le_of_ne (le_of_not_gt h) hne⟩

lemma orientation_flip_sorted {n r : ℕ} (f : PantsLabels n r) (b : Fin r → Bool) :
    pairOrientation ((pairFlip b).toEmbedding.trans f.val) = b := by
  funext i
  have h := f.property i
  cases hb : b i
  · simp [pairOrientation, pairFlip, hb, not_lt.mpr h.le]
  · simp [pairOrientation, pairFlip, hb, h]

def pantsLabelOrientationEquiv (n r : ℕ) :
    ((Fin r × Fin 2) ↪ Fin n) ≃ PantsLabels n r × (Fin r → Bool) where
  toFun f := (sortPairEmbedding f, pairOrientation f)
  invFun p := (pairFlip p.2).toEmbedding.trans p.1.val
  left_inv f := by
    apply Function.Embedding.ext
    intro p
    change f (pairFlip (pairOrientation f) (pairFlip (pairOrientation f) p)) = f p
    rw [pairFlip_self]
  right_inv p := by
    rcases p with ⟨f, b⟩
    have ho := orientation_flip_sorted f b
    apply Prod.ext
    · apply Subtype.ext
      apply Function.Embedding.ext
      intro q
      change f.val (pairFlip b (pairFlip (pairOrientation
        ((pairFlip b).toEmbedding.trans f.val)) q)) = f.val q
      rw [ho, pairFlip_self]
    · exact ho

/-- The tuple of curves is ordered: only the 2 orientations of each cusp pair
are divided out. There is no factor r!. -/
theorem pantsLabels_card (n r : ℕ) :
    Fintype.card (PantsLabels n r) * 2^r = n.descFactorial (2*r) := by
  have hc := Fintype.card_congr (pantsLabelOrientationEquiv n r)
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_embedding_eq,
    Fintype.card_fun, Fintype.card_bool, mul_comm r 2] using hc.symm

end WP.RandomGeometry
