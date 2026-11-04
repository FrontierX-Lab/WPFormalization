import WPFormalization.HigherOrder.FiniteSeries
import WPFormalization.Statements.Coefficients

/-! The actual finite-order triangular algorithm of Appendix C, Eqs.C.13--C.18.

At order K the profile is computed from orders <K, then the cusp scalar from the
new profile, then the genus scalar at p≥2, followed by descent to p=1 and p=0.
A fixed coordinate-increment path makes every coefficient a genuine defined
quantity. Path independence, analyticity, summability and actual remainders are
new mathematical obligations; none is included as an input field.
-/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

/-- Formal profile, cusp scalar and genus scalar at one already constructed order. -/
structure HierarchyJet where
  profile : List ℕ → Series
  cusp : ℕ → Series
  genus : ℕ → Series

/-- All three constant coefficients in Eq.C.13 are 1. -/
def baseJet : HierarchyJet := ⟨fun _ => 1, fun _ => 1, fun _ => 1⟩

/-- The coefficient b_d=(1/3)[z^(d-1)]barH, valid also at the critical endpoint. -/
def bCoeff (Y : ℝ) (d : ℕ) : ℝ :=
  if d = 0 then 0 else realCoeff (barH Y) (d-1)/3

/-- Bounded-component W_{j,q}(d), not an arbitrary auxiliary coefficient. -/
def smallW (P : PsiTheory) (Y : ℝ) (j : ℕ) (d : List ℕ) : ℝ :=
  (4 : ℝ)^j * normalized P j d Y

/-- Keep the marking labels in their original order. -/
def selectedNat (d : List ℕ) (I : Finset ℕ) : List ℕ :=
  ((List.range d.length).filter (fun i => i ∈ I)).map (fun i => d[i]!)

/-- Exact formal ratio in Eq.C.14; r_*=2j+s is the complexity loss. -/
def ratioSeries (Y : ℝ) (F : HierarchyJet) (p j s : ℕ) : Series :=
  let r := 2*j+s
  (C (A Y)*PowerSeries.X)^r *
    (∏ a ∈ Finset.range r,
      complexityShift (r-a) (F.cusp (p-s+a)) * (1-C ((r-a : ℕ) : ℝ)*PowerSeries.X)⁻¹) *
    ∏ b ∈ Finset.range j, F.genus (p+2*b)

/-- Merger contribution in Eq.C.15 with a distinguished first marking. -/
def mergerSeries (Y : ℝ) (F : HierarchyJet) (t : ℕ) (d : List ℕ) : Series :=
  C (A Y)*shiftVariable 1*complexityShift 1 (F.cusp d.length) *
    ∑ j ∈ Finset.range d.length, C (2*(d[j]! : ℝ)+1) *
      coefficientSum (fun l =>
        if 1 ≤ t+d[j]!+l then
          C (weight Y l) * complexityShift 1 (F.profile ((t+d[j]!+l-1) :: d.eraseIdx j))
        else 0)

/-- Nonseparating contribution in Eq.C.15. -/
def nonseparatingSeries (Y : ℝ) (F : HierarchyJet) (t : ℕ) (d : List ℕ) : Series :=
  C (2*A Y)*shiftVariable 1*complexityShift 1 (F.cusp (d.length+2))*F.genus (d.length+1) *
    coefficientSum (fun l => C (weight Y l) *
      ∑ u ∈ Finset.range (t+l-1),
        complexityShift 1 (F.profile (u :: (t+l-2-u) :: d)))

/-- Separating contribution in Eq.C.16. Only losses 2≤2j+s≤K are retained.
The bounded component is oriented once, as in the paper; no extra factor 1/2. -/
def separatingSeries (P : PsiTheory) (Y : ℝ) (F : HierarchyJet)
    (K t : ℕ) (d : List ℕ) : Series :=
  ∑ j ∈ Finset.range (K+1), ∑ I ∈ (Finset.range d.length).powerset,
    if Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ K then
      ratioSeries Y F (d.length+1) j I.card *
        coefficientSum (fun l => C (weight Y l) *
          ∑ u ∈ Finset.range (t+l-1),
            C (smallW P Y j (u :: selectedNat d I)) *
              complexityShift (2*j+I.card)
                (F.profile ((t+l-2-u) :: selectedNat d ((Finset.range d.length) \ I))))
    else 0

/-- The exact order-K adjacent increment prescribed by Eq.C.17. -/
def adjacentCoefficient (P : PsiTheory) (Y : ℝ) (F : HierarchyJet)
    (K i : ℕ) (d : List ℕ) : ℝ :=
  let t := d[i]!
  let tail := d.eraseIdx i
  show ℝ from -(PowerSeries.coeff K (mergerSeries Y F t tail + nonseparatingSeries Y F t tail +
    separatingSeries P Y F K t tail))

/-- State just before the t-th increment of coordinate i, filling coordinates from left to right. -/
def beforeCoordinate (d : List ℕ) (i t : ℕ) : List ℕ :=
  List.ofFn (fun j : Fin d.length => if j.val < i then d[j.val]! else if j.val = i then t else 0)

/-- Integrate adjacent increments along the fixed path allowed in Eq.C.17. -/
def profileAtOrder (P : PsiTheory) (Y : ℝ) (F : HierarchyJet) (K : ℕ) (d : List ℕ) : ℝ :=
  ∑ i ∈ Finset.range d.length, ∑ t ∈ Finset.range d[i]!,
    adjacentCoefficient P Y F K i (beforeCoordinate d i t)

/-- Dilaton rule Eq.C.17, with child complexity h+1, hence shift c=-1. -/
def cuspSeries (Y : ℝ) (profiles : List ℕ → Series) (p : ℕ) : Series :=
  C (A Y)⁻¹ * coefficientSum (fun d =>
    C (bCoeff Y (d+1))*complexityShift (-1) (profiles ((d+1) :: List.replicate p 0)))

/-- KdV rule Eq.C.18 at p≥2. Scalar ratios here use already computed lower orders. -/
def genusSeries (P : PsiTheory) (Y : ℝ) (F : HierarchyJet)
    (profiles : List ℕ → Series) (K p : ℕ) : Series :=
  profiles (1 :: List.replicate (p-1) 0) -
    C 3 * ∑ j ∈ Finset.range (K+1), ∑ s ∈ Finset.range (p-1),
      if Stable j (s+2) ∧ 1 ≤ 2*j+s ∧ 2*j+s ≤ K then
        C ((Nat.choose (p-2) s : ℝ) * smallW P Y j (List.replicate (s+2) 0)) *
          ratioSeries Y F p j s
      else 0

/-- Exact descent at unchanged parent complexity, including the h+1 shift. -/
def descendGenus (cusps : ℕ → Series) (next : Series) (p : ℕ) : Series :=
  complexityShift (-1) next * cusps (p+2) * (cusps p)⁻¹

/-- Construct the next coefficient in the prescribed triangular order. -/
def nextJet (P : PsiTheory) (Y : ℝ) (K : ℕ) (F : HierarchyJet) : HierarchyJet :=
  let profiles := fun d => setCoeff (F.profile d) K (profileAtOrder P Y F K d)
  let cusps := fun p => setCoeff (F.cusp p) K (PowerSeries.coeff K (cuspSeries Y profiles p))
  let highGenus := fun p => setCoeff (F.genus p) K (PowerSeries.coeff K (genusSeries P Y F profiles K p))
  let genus₁ := setCoeff (F.genus 1) K (PowerSeries.coeff K (descendGenus cusps (highGenus 2) 1))
  let genus₀ := setCoeff (F.genus 0) K (PowerSeries.coeff K (descendGenus cusps genus₁ 0))
  ⟨profiles, cusps, fun p => if p = 0 then genus₀ else if p = 1 then genus₁ else highGenus p⟩

/-- This is a Nat recursion, not a fixed-point assumption or unspecified coefficient family. -/
def hierarchyJet (P : PsiTheory) (Y : ℝ) : ℕ → HierarchyJet
  | 0 => baseJet
  | k+1 => nextJet P Y (k+1) (hierarchyJet P Y k)

/-- Canonical coefficients obtained from the exact order at which each is constructed. -/
def profileCoefficient (P : PsiTheory) (Y : ℝ) (d : List ℕ) (k : ℕ) : ℝ :=
  PowerSeries.coeff k ((hierarchyJet P Y k).profile d)
def cuspCoefficient (P : PsiTheory) (Y : ℝ) (p k : ℕ) : ℝ :=
  PowerSeries.coeff k ((hierarchyJet P Y k).cusp p)
def genusCoefficient (P : PsiTheory) (Y : ℝ) (p k : ℕ) : ℝ :=
  PowerSeries.coeff k ((hierarchyJet P Y k).genus p)

/- Formal series of Eq.C.13. No assertion about convergence of this series. -/
@[blueprint "eq:FE1"]
def formalProfile (P : PsiTheory) (Y : ℝ) (d : List ℕ) : Series :=
  PowerSeries.mk (profileCoefficient P Y d)
@[blueprint "eq:FE1"]
def formalCusp (P : PsiTheory) (Y : ℝ) (p : ℕ) : Series :=
  PowerSeries.mk (cuspCoefficient P Y p)
@[blueprint "eq:FE1"]
def formalGenus (P : PsiTheory) (Y : ℝ) (p : ℕ) : Series :=
  PowerSeries.mk (genusCoefficient P Y p)

@[simp] theorem profileCoefficient_zero (P : PsiTheory) (Y : ℝ) (d : List ℕ) :
    profileCoefficient P Y d 0 = 1 := by simp [profileCoefficient,hierarchyJet,baseJet]
@[simp] theorem cuspCoefficient_zero (P : PsiTheory) (Y : ℝ) (p : ℕ) :
    cuspCoefficient P Y p 0 = 1 := by simp [cuspCoefficient,hierarchyJet,baseJet]
@[simp] theorem genusCoefficient_zero (P : PsiTheory) (Y : ℝ) (p : ℕ) :
    genusCoefficient P Y p 0 = 1 := by simp [genusCoefficient,hierarchyJet,baseJet]

@[simp] theorem formalProfile_constant (P : PsiTheory) (Y : ℝ) (d : List ℕ) :
    constantCoeff (formalProfile P Y d) = 1 := by
  simp [formalProfile, ← coeff_zero_eq_constantCoeff]
@[simp] theorem formalCusp_constant (P : PsiTheory) (Y : ℝ) (p : ℕ) :
    constantCoeff (formalCusp P Y p) = 1 := by
  simp [formalCusp, ← coeff_zero_eq_constantCoeff]
@[simp] theorem formalGenus_constant (P : PsiTheory) (Y : ℝ) (p : ℕ) :
    constantCoeff (formalGenus P Y p) = 1 := by
  simp [formalGenus, ← coeff_zero_eq_constantCoeff]

/-- A later stage cannot change a coefficient that has already been constructed. -/
theorem hierarchy_profile_stable (P : PsiTheory) (Y : ℝ) (d : List ℕ)
    (n k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k ((hierarchyJet P Y n).profile d) = profileCoefficient P Y d k := by
  induction n with
  | zero => simpa [profileCoefficient, show k = 0 by omega] using (rfl :
      PowerSeries.coeff 0 ((hierarchyJet P Y 0).profile d) =
        PowerSeries.coeff 0 ((hierarchyJet P Y 0).profile d))
  | succ n ih =>
      by_cases h : k = n+1
      · subst k; rfl
      · have hkn : k ≤ n := by omega
        change PowerSeries.coeff k
          (setCoeff ((hierarchyJet P Y n).profile d) (n+1)
            (profileAtOrder P Y (hierarchyJet P Y n) (n+1) d)) = _
        rw [setCoeff_other _ _ _ _ h]
        exact ih hkn

/-- Every constructed jet retains the unit normalization of all three series. -/
theorem hierarchy_unit_constants (P : PsiTheory) (Y : ℝ) (n : ℕ) :
    (∀ d, constantCoeff ((hierarchyJet P Y n).profile d) = 1) ∧
    (∀ p, constantCoeff ((hierarchyJet P Y n).cusp p) = 1) ∧
    (∀ p, constantCoeff ((hierarchyJet P Y n).genus p) = 1) := by
  induction n with
  | zero => simp [hierarchyJet,baseJet]
  | succ n ih =>
      constructor
      · intro d
        simpa [hierarchyJet,nextJet] using ih.1 d
      constructor
      · intro p
        simpa [hierarchyJet,nextJet] using ih.2.1 p
      · intro p
        by_cases hp₀ : p = 0
        · subst p
          simpa [hierarchyJet,nextJet] using ih.2.2 0
        · by_cases hp₁ : p = 1
          · subst p
            simpa [hierarchyJet,nextJet] using ih.2.2 1
          · simpa [hierarchyJet,nextJet,hp₀,hp₁] using ih.2.2 p

/-- Eq.11.7 with the actual triangular cusp coefficients. Only marked coefficients remain an input. -/
def unmarkedSeries (P : PsiTheory) (marked₁ : Series) : Series :=
  unmarkedProduct (formalCusp P 0 0) marked₁

theorem unmarkedSeries_constant (P : PsiTheory) (marked₁ : Series)
    (hm : constantCoeff marked₁ = 1) : constantCoeff (unmarkedSeries P marked₁) = 1 := by
  exact unmarkedProduct_constant _ _ (formalCusp_constant P 0 0) hm

end WP.HigherOrder
