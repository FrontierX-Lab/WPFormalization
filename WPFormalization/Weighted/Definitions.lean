import WPFormalization.Statements.Comparison

/-! The unchanged numerical definitions used by the weighted bounds of §5.
Keeping definitions separate allows the original theorem module to consume
proved model-normalization and transition helpers without an import cycle. -/
noncomputable section
namespace WP

def validModel (g : ℕ) (d : List ℤ) (Y : ℝ) : ℝ :=
  if (∀ k ∈ d, 0 ≤ k) ∧ Stable g d.length ∧
      (d.map Int.toNat).sum ≤ dimension g d.length then model g (d.map Int.toNat) Y else 0

def signedWeight (c : ℝ) (d : List ℤ) : ℝ := clippedWeight c (d.map Int.toNat)

/- Blueprint label(s): lem:weighted-linear
Paper v3: 5.4 [PDF 27]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:weighted-linear"]
def PivotChoice (pivot : ℕ) (d : List ℕ) : Prop :=
  2 ≤ pivot ∨ (pivot = 1 ∧ ∀ k ∈ d, k ≤ 1) ∨ (pivot = 0 ∧ ∀ k ∈ d, k = 0)

/- Blueprint label(s): lem:weighted-linear
Paper v3: 5.4 [PDF 27]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:weighted-linear"]
def weightedLinear (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) : ℝ :=
  let parent := pivot :: d
  let m := deficit g parent
  let factor := fun g' ds => validModel g' ds Y/model g parent Y *
    signedWeight c ds/clippedWeight c parent
  (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1) *
    ∑ l ∈ Finset.range (m+1), theta Y l * factor g
      (((pivot : ℤ)+d[j]!+l-1) :: (d.eraseIdx j).map Int.ofNat)) +
  (if g = 0 then 0 else (1/2 : ℝ) * ∑ l ∈ Finset.range (m+1), theta Y l *
    ∑ u ∈ Finset.range (pivot+l-1), factor (g-1)
      ((u : ℤ) :: ((pivot : ℤ)+l-2-u) :: d.map Int.ofNat))

/- Blueprint label(s): lem:weighted-separating
Paper v3: 5.5 [PDF 27]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:weighted-separating"]
def weightedSeparating (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) : ℝ :=
  let parent := pivot :: d
  let m := deficit g parent
  (1/2 : ℝ) * ∑ l ∈ Finset.range (m+1), theta Y l *
    ∑ u ∈ Finset.range (pivot+l-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        let d₁ := (u : ℤ) :: selected (d.map Int.ofNat) I
        let d₂ := ((pivot : ℤ)+l-2-u) :: selected (d.map Int.ofNat) ((Finset.range d.length) \ I)
        validModel g₁ d₁ Y*validModel (g-g₁) d₂ Y/model g parent Y *
          signedWeight c d₁*signedWeight c d₂/clippedWeight c parent *
          Real.exp ((1/12 : ℝ)*min (complexity g₁ d₁.length) (complexity (g-g₁) d₂.length))

end WP
