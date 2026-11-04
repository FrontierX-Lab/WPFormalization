import WPFormalization.Statements.Parameter

/-! An explicit *abstract numerical* psi-intersection interface.

The fields are the classical string/dilaton/DVV identities with dimension and
symmetry, not hypotheses of the paper's new estimates. No inhabitant is asserted.
Concrete DM cotangent classes, integration and WP geometry instances remain
unconstructed. Results parametrized only by `P : PsiTheory` are conditional
numerical statements. The additional classical realization interfaces give
the geometric identifications proved downstream in `Geometry/Bridge.lean`.
-/
noncomputable section
namespace WP

def selected (d : List ℤ) (I : Finset ℕ) : List ℤ :=
  ((List.range d.length).filter (fun i => i ∈ I)).map (fun i => d[i]!)
def doubleWeight (d : List ℤ) : ℝ := (d.map (fun k => (oddFactorial k.toNat : ℝ))).prod

def weighted (psi : ℕ → List ℤ → ℝ) (g : ℕ) (d : List ℤ) : ℝ :=
  doubleWeight d * psi g d

/-- The exact finite RHS of the weighted pivot equation, including unstable zero factors. -/
def dvvRHS (psi : ℕ → List ℤ → ℝ) (g pivot : ℕ) (d : List ℤ) : ℝ :=
  (∑ j ∈ Finset.range d.length,
    (2*(d[j]! : ℝ)+1) * weighted psi g
      (((pivot : ℤ)+d[j]!-1) :: (d.eraseIdx j))) +
  (if g = 0 then 0 else (1/2 : ℝ) * ∑ u ∈ Finset.range (pivot-1),
    weighted psi (g-1) ((u : ℤ) :: ((pivot : ℤ)-2-u) :: d)) +
  (1/2 : ℝ) * ∑ u ∈ Finset.range (pivot-1),
    ∑ g₁ ∈ Finset.range (g+1), ∑ I ∈ (Finset.range d.length).powerset,
      weighted psi g₁ ((u : ℤ) :: selected d I) *
      weighted psi (g-g₁) (((pivot : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I))

/- Abstract classical intersection-number laws. There is deliberately no global chosen instance. -/
@[blueprint "ext:dvv"]
structure PsiTheory where
  psi : ℕ → List ℤ → ℝ
  vanish : ∀ g d, (¬ Stable g d.length ∨ (∃ k ∈ d, k < 0) ∨
    d.sum ≠ (3*(g : ℤ)-3+d.length)) → psi g d = 0
  symmetry : ∀ g d e, d.Perm e → psi g d = psi g e
  base₀ : psi 0 [0,0,0] = 1
  base₁ : psi 1 [1] = 1/24
  string : ∀ g d, Stable g d.length →
    psi g (0 :: d) = ∑ j ∈ Finset.range d.length, psi g (d.set j (d[j]!-1))
  dilaton : ∀ g d, Stable g d.length →
    psi g (1 :: d) = (2*(g : ℝ)-2+d.length) * psi g d
  dvv : ∀ (g pivot : ℕ) (d : List ℤ), (∀ k ∈ d, 0 ≤ k) →
    2 ≤ complexity g (d.length+1) →
    weighted psi g ((pivot : ℤ) :: d) = dvvRHS psi g pivot d

def pure (P : PsiTheory) (g : ℕ) (d : List ℕ) : ℝ := P.psi g (d.map Int.ofNat)

/- Eq.4.3. This is a normalization of interface psi numbers, not a construction of moduli. -/
/- Blueprint label(s): eq:H4
Paper v3: 4.3 [PDF 19]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H4"]
def pureC (P : PsiTheory) (g : ℕ) (d : List ℕ) : ℝ :=
  (4 : ℝ)^g * (d.map (fun k => (oddFactorial k : ℝ))).prod /
    (3^(complexity g d.length) * Real.Gamma (complexity g d.length)) * pure P g d

/- Multiplicity vectors for background insertions k=2,...,m+1. -/
/- Blueprint label(s): eq:H6
Paper v3: 4.5 [PDF 20]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H6"]
def backgrounds (m : ℕ) : Finset (Fin m → ℕ) :=
  (Finset.univ.image (fun l : Fin m → Fin (m+1) => fun i => (l i).val)).filter
    (fun l => ∑ i : Fin m, (i.val+1)*l i = m)
/- Blueprint label(s): eq:H6
Paper v3: 4.5 [PDF 20]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H6"]
def backgroundDegrees {m : ℕ} (l : Fin m → ℕ) : List ℕ :=
  (List.finRange m).flatMap (fun i => List.replicate (l i) (i.val+2))

/- Eq.4.5, the finite background sum, with stable and dimension zero conventions. -/
/- Blueprint label(s): eq:H6
Paper v3: 4.5 [PDF 20]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H6"]
def shifted (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  if Stable g d.length ∧ d.sum ≤ dimension g d.length then
    (d.map (fun k => (oddFactorial k : ℝ))).prod *
    ∑ l ∈ backgrounds (deficit g d),
      pure P g (d ++ backgroundDegrees l) *
      (∏ i : Fin (deficit g d),
        (-(iteratedDeriv (i.val+2) X Y).re)^(l i)/(l i).factorial) /
      a Y ^ (complexity g d.length + ∑ i, l i)
  else 0

/-- Eq.4.4 numerical mixed bracket defined by the classical finite transform.
Its identification with a DM integral under the explicit classical realization
interface is proved in `Geometry/Bridge.lean`; no concrete realization is chosen. -/
def mixedBracket (P : PsiTheory) (g : ℕ) (d : List ℕ) : ℝ :=
  (4 : ℝ)^d.sum * (2*Real.pi^2)^(deficit g d) * shifted P g d 0

/- Interior Eq.4.6 and canonical continuous endpoint (only degree-two backgrounds survive). -/
/- Blueprint label(s): eq:H7
Paper v3: 4.6 [PDF 20]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H7"]
def normalized (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  if Y = y₀ then
    if Stable g d.length ∧ d.sum ≤ dimension g d.length then
      (3 : ℝ)^(deficit g d) *
        (d.map (fun k => (oddFactorial k : ℝ))).prod *
        pure P g (d ++ List.replicate (deficit g d) 2) / (deficit g d).factorial
    else 0
  else a Y^(complexity g d.length) * r Y^(deficit g d) * shifted P g d Y

/- Coefficients of the harmonic model, Eq.4.11. -/
/- Blueprint label(s): eq:H12
Paper v3: 4.11 [PDF 22]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H12"]
def harmonicCoeff (Y : ℝ) (h m : ℕ) : ℝ :=
  realCoeff (fun z => (barH Y z)⁻¹^h) m
/- Blueprint label(s): eq:H12
Paper v3: 4.11 [PDF 22]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H12"]
def model (g : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  (3 : ℝ)^(complexity g d.length) * Real.Gamma (complexity g d.length) /
    4^g * harmonicCoeff Y (complexity g d.length) (deficit g d)
/- Blueprint label(s): eq:H12
Paper v3: 4.11 [PDF 22]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H12"]
def ratio (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  normalized P g d Y / model g d Y

lemma backgrounds_zero : backgrounds 0 = {0} := by
  ext l
  have hl : l = 0 := Subsingleton.elim _ _
  subst l
  simp [backgrounds]
  exact Subsingleton.elim _ _
lemma backgrounds_one : backgrounds 1 = {fun _ => 1} := by
  ext l
  constructor
  · intro hl
    have hs := (Finset.mem_filter.mp hl).2
    have he : l = fun _ => 1 := by
      funext i
      fin_cases i
      simpa using hs
    exact Finset.mem_singleton.mpr he
  · intro hl
    have he := Finset.mem_singleton.mp hl
    subst l
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨fun _ => (1 : Fin 2), Finset.mem_univ _, rfl⟩, ?_⟩
    simp
lemma psi_1_0_2 (P : PsiTheory) : P.psi 1 [0,2] = 1/24 := by
  have hs := P.string 1 [2] (by norm_num [Stable])
  norm_num [Finset.sum_range_succ] at hs
  exact hs.trans P.base₁
private lemma normalized_base_zero_interior (P : PsiTheory) (Y : ℝ) (ha : a Y ≠ 0) (hy : Y ≠ y₀) :
    normalized P 0 [0,0,0] Y = 1 := by
  dsimp [normalized, shifted, Stable, dimension, deficit, complexity]
  norm_num [hy, backgrounds_zero, backgroundDegrees, pure, oddFactorial,
    Finset.prod_range_succ, P.base₀, ha]
private lemma normalized_base_one_interior (P : PsiTheory) (Y : ℝ) (ha : a Y ≠ 0) (hy : Y ≠ y₀) :
    normalized P 1 [1] Y = 1/8 := by
  dsimp [normalized, shifted, Stable, dimension, deficit, complexity]
  norm_num [hy, backgrounds_zero, backgroundDegrees, pure, oddFactorial,
    Finset.prod_range_succ, P.base₁, ha]
  field_simp [ha]
  <;> ring
private lemma normalized_zero_one_interior (P : PsiTheory) (Y : ℝ) (ha : a Y ≠ 0) (hy : Y ≠ y₀) :
    normalized P 1 [0] Y = -(iteratedDeriv 2 X Y).re*r Y/(24*a Y) := by
  rw [normalized, if_neg hy]
  change a Y^1*r Y^1 * (([0].map (fun k => (oddFactorial k : ℝ))).prod *
    ∑ l ∈ backgrounds 1, pure P 1 ([0] ++ backgroundDegrees l) *
      (∏ i : Fin 1, (-(iteratedDeriv (i.val+2) X Y).re)^(l i)/(l i).factorial) /
      a Y^(1+∑ i : Fin 1, l i)) = _
  norm_num [backgrounds_one, backgroundDegrees, pure, oddFactorial,
    Finset.prod_range_succ, psi_1_0_2, List.finRange_succ,
    Fin.prod_univ_one, Fin.sum_univ_one]
  field_simp [ha]
  <;> ring
private lemma normalized_base_zero_critical (P : PsiTheory) (Y : ℝ) (hy : Y = y₀) :
    normalized P 0 [0,0,0] Y = 1 := by
  norm_num [normalized, hy, Stable, dimension, deficit, complexity,
    pure, oddFactorial, Finset.prod_range_succ, P.base₀]
private lemma normalized_base_one_critical (P : PsiTheory) (Y : ℝ) (hy : Y = y₀) :
    normalized P 1 [1] Y = 1/8 := by
  norm_num [normalized, hy, Stable, dimension, deficit, complexity,
    pure, oddFactorial, Finset.prod_range_succ, P.base₁]
private lemma normalized_zero_one_critical (P : PsiTheory) (Y : ℝ) (hy : Y = y₀) :
    normalized P 1 [0] Y = 1/8 := by
  norm_num [normalized, hy, Stable, dimension, deficit, complexity,
    pure, oddFactorial, Finset.prod_range_succ, psi_1_0_2, List.finRange_succ, Finset.card_univ, Fintype.card_fin, deficit, dimension]

/- Eq.4.9. -/
/- Blueprint label(s): eq:H10
Paper v3: 4.9 [PDF 22]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H10"]
theorem initial_amplitudes (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    normalized P 0 [0,0,0] Y = 1 ∧ normalized P 1 [1] Y = 1/8 ∧
    normalized P 1 [0] Y = theta Y 1/8 := by
  by_cases hy : Y = y₀
  · refine ⟨normalized_base_zero_critical P Y hy,
      normalized_base_one_critical P Y hy, ?_⟩
    rw [normalized_zero_one_critical P Y hy, hy, critical_kernels.2 1]
  · have hi : Y ∈ Set.Ico 0 y₀ := ⟨hY.1, lt_of_le_of_ne hY.2 hy⟩
    have ha := a_ne_zero Y hi
    refine ⟨normalized_base_zero_interior P Y ha hy,
      normalized_base_one_interior P Y ha hy, ?_⟩
    rw [normalized_zero_one_interior P Y ha hy, theta_one Y hi]
    ring

/- Eq.4.4 as an identity in the numerical interface; the integral realization is not asserted. -/
/- Blueprint label(s): eq:H5
Paper v3: 4.4 [PDF 20]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H5"]
theorem mixed_transform (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hst : Stable g d.length) (hd : d.sum ≤ dimension g d.length) :
    mixedBracket P g d / ((4 : ℝ)^d.sum*(2*Real.pi^2)^(deficit g d)) =
      (d.map (fun k => (oddFactorial k : ℝ))).prod *
      ∑ l ∈ backgrounds (deficit g d), pure P g (d ++ backgroundDegrees l) *
        ∏ i : Fin (deficit g d),
          (((-1 : ℝ)^(i.val+2)/(i.val+1).factorial)^(l i))/(l i).factorial := by
  have hscale : (4 : ℝ)^d.sum*(2*Real.pi^2)^(deficit g d) ≠ 0 := by positivity
  unfold mixedBracket
  rw [mul_div_cancel_left₀ _ hscale]
  unfold shifted
  rw [if_pos ⟨hst, hd⟩, a_zero]
  simp only [one_pow, div_one]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Complex.ofReal_zero]
  rw [iteratedDeriv_X_zero_re (i.val+2) (by omega)]
  have he : i.val+2-1 = i.val+1 := by omega
  rw [he, ← neg_div]
  have hs : -((-1 : ℝ)^(i.val+1)) = (-1)^(i.val+2) := by simp [pow_succ]
  rw [hs]

end WP
