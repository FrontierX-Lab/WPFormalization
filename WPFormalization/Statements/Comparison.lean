import WPFormalization.Statements.PrimitiveBounds
import WPFormalization.Statements.IntersectionInterface
import WPFormalization.Analysis.HarmonicMass
import WPFormalization.Intersection.TopDegree
import WPFormalization.Intersection.PositiveRecursion

/-! Exact positive recursion and comparison statements on the explicit psi interface.
The parameter `P` is visible in every assertion about intersection amplitudes. -/
noncomputable section
namespace WP

/-- Signed degrees are tested before conversion to naturals. -/
def normInt (P : PsiTheory) (g : ℕ) (d : List ℤ) (Y : ℝ) : ℝ :=
  if ∀ k ∈ d, 0 ≤ k then normalized P g (d.map Int.toNat) Y else 0

/- Blueprint label(s): eq:H9
Paper v3: 4.8 [PDF 21]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H9"]
def positiveRHS (P : PsiTheory) (g pivot : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  let m := deficit g (pivot :: d)
  (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1) *
    ∑ l ∈ Finset.range (m+1), theta Y l * normInt P g
      (((pivot : ℤ)+d[j]!+l-1) :: ((d.eraseIdx j).map Int.ofNat)) Y) +
  (if g = 0 then 0 else (1/2 : ℝ) * ∑ l ∈ Finset.range (m+1), theta Y l *
    ∑ u ∈ Finset.range (pivot+l-1), normInt P (g-1)
      ((u : ℤ) :: ((pivot : ℤ)+l-2-u) :: d.map Int.ofNat) Y) +
  (1/2 : ℝ) * ∑ l ∈ Finset.range (m+1), theta Y l *
    ∑ u ∈ Finset.range (pivot+l-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        normInt P g₁ ((u : ℤ) :: selected (d.map Int.ofNat) I) Y *
        normInt P (g-g₁) (((pivot : ℤ)+l-2-u) ::
          selected (d.map Int.ofNat) ((Finset.range d.length) \ I)) Y

/- The explicit paper RHS is the kernel-weighted convolution of its child sums. -/
lemma positiveRHS_convolution (P : PsiTheory) (g pivot : ℕ) (d : List ℕ) (Y : ℝ) :
    positiveRHS P g pivot d Y =
      ∑ l ∈ Finset.range (deficit g (pivot :: d)+1), theta Y l*
        normalizedChildren P g (pivot+l) (d.map Int.ofNat) Y := by
  unfold positiveRHS normalizedChildren
  simp only [List.length_map, mul_add, Finset.sum_add_distrib]
  apply congrArg₂ (fun a b : ℝ => a+b)
  · apply congrArg₂ (fun a b : ℝ => a+b)
    · simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hget : (d.map Int.ofNat)[j]! = (d[j]! : ℤ) := by simp [hj']
      rw [hget, List.eraseIdx_map]
      simp only [Int.cast_natCast]
      have he : (((pivot+l : ℕ) : ℤ)+(d[j]! : ℤ)-1) =
          (pivot : ℤ)+d[j]!+l-1 := by push_cast; ring
      rw [he]
      unfold normInt
      ring
    · by_cases hg : g = 0
      · simp [hg]
      · simp only [hg, ite_false, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro u hu
        simp only [normInt, Nat.cast_add]
        ring
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro g₁ hg₁
    apply Finset.sum_congr rfl
    intro I hI
    simp only [normInt, Nat.cast_add]
    ring

/- The zero-deficit specialization, proved directly from classical DVV. -/
lemma positive_recursion_top (P : PsiTheory) (g pivot : ℕ) (d : List ℕ) (Y : ℝ)
    (hh : 2 ≤ complexity g (d.length+1))
    (hd : (pivot :: d).sum = dimension g (d.length+1)) (hY : Y ∈ Set.Icc 0 y₀) :
    normalized P g (pivot :: d) Y = positiveRHS P g pivot d Y := by
  have hst : Stable g (d.length+1) := by unfold complexity at hh; unfold Stable; omega
  have htop : ((pivot : ℤ) :: d.map Int.ofNat).sum =
      3*(g : ℤ)-3+((pivot : ℤ) :: d.map Int.ofNat).length := by
    have hi := congrArg (fun n : ℕ => (n : ℤ)) hd
    rw [dimension_cast_of_stable g (d.length+1) hst] at hi
    simpa only [List.sum_cons, List.length_cons, List.length_map, sum_map_int,
      Nat.cast_add, Nat.cast_one] using hi
  have hm : deficit g (pivot :: d) = 0 := by simp [deficit, hd, Nat.add_comm]
  have ht : theta Y 0 = 1 := by simp [theta, realCoeff, coeff, barK_zero_closed Y hY]
  rw [normalized_top P g (pivot :: d) Y hY (by simpa [Nat.add_comm] using hd)]
  have hv := P.dvv g pivot (d.map Int.ofNat) (by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    exact Int.natCast_nonneg j) (by simpa using hh)
  rw [show (pivot :: d).map Int.ofNat = (pivot : ℤ) :: d.map Int.ofNat from rfl, hv]
  unfold positiveRHS
  simp only [hm, Finset.range_one, Finset.sum_singleton, ht, one_mul, zero_add, add_zero]
  unfold dvvRHS
  simp only [List.length_map, normInt]
  apply congrArg₂ (fun a b : ℝ => a+b)
  · apply congrArg₂ (fun a b : ℝ => a+b)
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < d.length := Finset.mem_range.mp hj
      have hget : (d.map Int.ofNat)[j]! = (d[j]! : ℤ) := by simp [hj']
      rw [hget, List.eraseIdx_map]
      simp only [Int.cast_natCast]
      congr 1
      symm
      exact signed_normalized_top P g _ Y hY
        (by simpa [hget, List.eraseIdx_map] using merger_dimension g pivot (d.map Int.ofNat) htop j (by simpa using hj'))
    · by_cases hg : g = 0
      · simp [hg]
      · simp only [hg, ite_false]
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        symm
        exact signed_normalized_top P (g-1) _ Y hY
          (contraction_dimension g hg pivot (d.map Int.ofNat) htop u)
  · congr 1
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro g₁ hg₁
    apply Finset.sum_congr rfl
    intro I hI
    symm
    have hgg : g₁ ≤ g := by have := Finset.mem_range.mp hg₁; omega
    have hdim := separating_dimension g g₁ hgg pivot (d.map Int.ofNat) htop u I
    exact signed_normalized_product_top P g₁ (g-g₁) _ _ Y hY
      (by simpa only [List.length_map, Nat.cast_zero, add_zero] using hdim)

/- Eq.4.8. Stable, admissible, noninitial states; ordered separating splits. -/
/- Blueprint label(s): eq:H9
Paper v3: 4.8 [PDF 21]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H9"]
theorem positive_recursion (P : PsiTheory) (g pivot : ℕ) (d : List ℕ) (Y : ℝ)
    (hh : 2 ≤ complexity g (d.length+1))
    (hd : (pivot :: d).sum ≤ dimension g (d.length+1)) (hY : Y ∈ Set.Icc 0 y₀) :
    normalized P g (pivot :: d) Y = positiveRHS P g pivot d Y := by
  rw [positiveRHS_convolution]
  exact normalized_positive_convolution P g pivot d Y hh hd hY

/- Blueprint label(s): eq:H13
Paper v3: 4.12 [PDF 22]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:H13"]
def linearQ (Y : ℝ) (h m l : ℕ) : ℝ :=
  theta Y l * harmonicCoeff Y (h-1) (m-l) / harmonicCoeff Y h m
/- Blueprint label(s): eq:H22
Paper v3: 4.21 [PDF 23]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:H22"]
def linearS₀ (Y : ℝ) (h m : ℕ) : ℝ := ∑ l ∈ Finset.range (m+1), linearQ Y h m l

/- Eq.4.12; finite m and h≥2, with no geometric premise. -/
/- Blueprint label(s): eq:H13
Paper v3: 4.12 [PDF 22]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:H13"]
theorem mass_identity (Y : ℝ) (h m : ℕ) (hh : 2 ≤ h) (hY : Y ∈ Set.Icc 0 y₀) :
    ∑ l ∈ Finset.range (m+1), linearQ Y h m l *
      (1 - 2*((m : ℝ)-l)/(3*((h : ℝ)-1))) = 1 := by
  simpa only [linearQ] using Analysis.harmonic_mass_identity Y h m hh hY

/- Actual linear mass for an all-zero parent, counting only valid mergers and contractions. -/
/- Blueprint label(s): eq:H14
Paper v3: 4.13 [PDF 23]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:H14"]
def zeroLinearMass (Y : ℝ) (g n : ℕ) : ℝ :=
  let h := complexity g n
  let m := dimension g n
  (∑ l ∈ Finset.range (m+1), linearQ Y h m l *
    (((n : ℝ)-1)*(if 1 ≤ l then 1 else 0) + 2*(l-1 : ℕ)) / (3*((h : ℝ)-1)))

/- Blueprint label(s): eq:H14
Paper v3: 4.13 [PDF 23]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:H14"]
theorem zero_mass_defect (Y : ℝ) (g n : ℕ) (hg : 2 ≤ g) (hn : 1 ≤ n)
    (hY : Y ∈ Set.Icc 0 y₀) :
    zeroLinearMass Y g n = 1 + (3-(n : ℝ))/(3*((complexity g n : ℝ)-1)) *
      harmonicCoeff Y (complexity g n-1) (dimension g n) /
        harmonicCoeff Y (complexity g n) (dimension g n) := by
  let h := complexity g n
  let m := dimension g n
  have hh : 2 ≤ h := by dsimp [h, complexity]; omega
  have hden : (3*((h : ℝ)-1)) ≠ 0 := by
    have : (2 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hne : (h : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hL : (n : ℝ) = 3*(h : ℝ)-2*(m : ℝ) := by
    dsimp [h, m, complexity, dimension]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hterm (l : ℕ) :
      linearQ Y h m l *
        (((n : ℝ)-1)*(if 1 ≤ l then 1 else 0)+2*(l-1 : ℕ)) /
          (3*((h : ℝ)-1)) =
      linearQ Y h m l * (1-2*((m : ℝ)-l)/(3*((h : ℝ)-1))) -
        (if l = 0 then ((n : ℝ)-3)/(3*((h : ℝ)-1))*linearQ Y h m 0 else 0) := by
    by_cases hl : l = 0
    · subst l
      norm_num only [Nat.zero_sub, Nat.cast_zero, mul_zero, add_zero, zero_div, sub_zero]
      simp only [ite_false, ite_true, mul_zero, zero_div, add_zero]
      rw [hL]
      field_simp [hne]
      ring
    · have hll : 1 ≤ l := by omega
      simp only [hll, ite_true, hl, ite_false, sub_zero]
      rw [Nat.cast_sub hll, Nat.cast_one, hL]
      field_simp [hne]
      ring
  unfold zeroLinearMass
  change (∑ l ∈ Finset.range (m+1), _ : ℝ) = _
  rw [Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_sub_distrib,
    mass_identity Y h m hh hY]
  have hsdelta :
      (∑ l ∈ Finset.range (m+1),
        if l = 0 then ((n : ℝ)-3)/(3*((h : ℝ)-1))*linearQ Y h m 0 else 0) =
      ((n : ℝ)-3)/(3*((h : ℝ)-1))*linearQ Y h m 0 := by simp
  rw [hsdelta]
  have ht : theta Y 0 = 1 := by
    by_cases hy : Y = y₀
    · simpa [hy] using critical_kernels.2 0
    · have hi : Y ∈ Set.Ico 0 y₀ := ⟨hY.1, lt_of_le_of_ne hY.2 hy⟩
      simp [theta, realCoeff, coeff, barK_zero Y hi]
  simp only [linearQ, ht, Nat.sub_zero, one_mul]
  dsimp [h, m]
  ring

/- Blueprint label(s): eq:H30
Paper v3: 5.8 [PDF 26]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:H30"]
def zeros (d : List ℕ) : ℕ := (d.filter (fun k => k = 0)).length
/- Blueprint label(s): eq:H30
Paper v3: 5.8 [PDF 26]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:H30"]
def inactive (d : List ℕ) : ℕ := (d.filter (fun k => k ≤ 1)).length
/- Eq.5.8. c is an explicit tuning parameter, not a hidden chosen constant. -/
/- Blueprint label(s): eq:H30
Paper v3: 5.8 [PDF 26]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:H30"]
def clippedWeight (c : ℝ) (d : List ℕ) : ℝ :=
  (4 : ℝ)^(zeros d) * ∏ j ∈ Finset.range (inactive d), max 1 (c*Real.sqrt (j+1))
def Terminal (g : ℕ) (d : List ℕ) : Prop := deficit g d = 0 ∨ g ≤ 1

end WP
