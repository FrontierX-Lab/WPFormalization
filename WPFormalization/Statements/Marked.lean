import WPFormalization.Intersection.ProfileMonotone
import WPFormalization.Analysis.KernelWeightMoments
import WPFormalization.Analysis.KernelAction
import WPFormalization.Statements.Comparison
import WPFormalization.Intersection.CriticalCoefficient
import WPFormalization.HigherOrder.NegativeBinomial
import WPFormalization.Analysis.DilatonCoefficients
import WPFormalization.HigherOrder.ShiftedDilaton
import WPFormalization.HigherOrder.ShiftedKdV

/-! Marked profiles and first-order estimates on the conditional numerical interface. -/
noncomputable section
namespace WP

/- Blueprint label(s): eq:TL9
Paper v3: 6.1 [PDF 31]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL9"]
def W (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  (4 : ℝ)^g * normalized P g (List.replicate p 0) Y
/- Blueprint label(s): eq:TL9
Paper v3: 6.1 [PDF 31]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL9"]
def profile (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  normalized P g d Y / normalized P g (List.replicate d.length 0) Y

/- Blueprint label(s): eq:TL12
Paper v3: 6.4 [PDF 31]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL12"]
def dilatonCoeff (Y : ℝ) (d : ℕ) : ℝ :=
  (iteratedDeriv d X Y).re * r Y^(d-1) / (a Y * oddFactorial d)

/- Blueprint label(s): eq:TL12
Paper v3: 6.4 [PDF 31]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL12"]
theorem shifted_dilaton (P : PsiTheory) (g p : ℕ) (hst : Stable g p)
    (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    (complexity g p : ℝ) * normalized P g (List.replicate p 0) Y =
      ∑ d ∈ Finset.range (dimension g (p+1)+1),
        if 1 ≤ d then dilatonCoeff Y d * normalized P g (d :: List.replicate p 0) Y else 0 := by
  simpa only [dilatonCoeff] using shifted_dilaton_proof P g p hst Y hY

/- Blueprint label(s): eq:TL12
Paper v3: 6.4 [PDF 31]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL12"]
theorem dilaton_coefficient (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) (d : ℕ) (hd : 1 ≤ d) :
    dilatonCoeff Y d = realCoeff (barH Y) (d-1)/3 := by
  rw [realCoeff_barH_interior Y (ne_of_lt hY.2)]
  have he : d-1+1 = d := by omega
  rw [he]
  unfold dilatonCoeff
  ring

/- Eq.6.6 requires at least two distinguished markings. -/
/- Blueprint label(s): eq:TL14
Paper v3: 6.6 [PDF 31]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL14"]
theorem shifted_kdv (P : PsiTheory) (g p : ℕ) (hg : 1 ≤ g) (hp : 2 ≤ p)
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    normalized P g (1 :: List.replicate (p-1) 0) Y =
      normalized P (g-1) (List.replicate (p+2) 0) Y / 4 +
      3/2 * ∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (p-1),
        (Nat.choose (p-2) s : ℝ) * normalized P j (List.replicate (s+2) 0) Y *
          normalized P (g-j) (List.replicate (p-s) 0) Y := by
  exact shifted_kdv_proof P g p hg hp Y hY

/- Lemma 6.1, including dimension-exceeding tuples, whose amplitudes are zero. -/
/- Blueprint label(s): lem:monotone
Paper v3: 6.1 [PDF 32]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:monotone"]
theorem profile_monotone (P : PsiTheory) (g : ℕ) (d : List ℕ) (hst : Stable g d.length)
    (i : ℕ) (hi : i < d.length) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    normalized P g (d.set i (d[i]!+1)) Y ≤ normalized P g d Y ∧
    0 ≤ profile P g d Y ∧ profile P g d Y ≤ 1 := by
  simpa only [profile] using profile_monotone_proof P g d hst i hi Y hY

/- Blueprint label(s): eq:TL19
Paper v3: 6.11 [PDF 32]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL19"]
def separatingS (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range p,
    (Nat.choose (p-1) s : ℝ) * W P j (s+1) Y * W P (g-j) (p-s) Y) / W P g p Y
/- Blueprint label(s): eq:TL19
Paper v3: 6.11 [PDF 32]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL19"]
def separatingT (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (p-1),
    (Nat.choose (p-2) s : ℝ) * W P j (s+2) Y * W P (g-j) (p-s) Y) / W P g p Y

/- Eq.7.1; these moments are defined from weights, not postulated functions. -/
/- Blueprint label(s): eq:PF1
Paper v3: 7.1 [PDF 35]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:PF1"]
def Theta (Y : ℝ) : ℝ := ∑' l : ℕ, weight Y l
/- Blueprint label(s): eq:PF1
Paper v3: 7.1 [PDF 35]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:PF1"]
def moment₁ (Y : ℝ) : ℝ := ∑' l : ℕ, (l : ℝ)*weight Y l
/- Blueprint label(s): eq:PF1
Paper v3: 7.1 [PDF 35]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:PF1"]
def Z (Y : ℝ) : ℝ := A Y*a Y*Real.rpow (r Y) (3/2 : ℝ)

/- Blueprint label(s): eq:PF1
Paper v3: 7.1 [PDF 35]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:PF1"]
theorem kernel_action_moments (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    Theta Y = -1/(deriv (barK Y) 1).re ∧
    moment₁ Y = (iteratedDeriv 2 (barK Y) 1).re/(2*(deriv (barK Y) 1).re^2) ∧
    Z Y = Real.sqrt 2*action Y := by
  have hYc:Y∈Set.Icc 0 y₀:=⟨hY.1,hY.2.le⟩
  refine ⟨?_,?_,?_⟩
  · simpa only [Theta] using Analysis.theta_sum_kernel_deriv Y hYc
  · simpa only [moment₁] using Analysis.first_weight_moment_kernel_deriv Y hYc
  · simpa only [Z] using Analysis.normalized_kernel_action Y hY

/- Eq.7.3, including the marking-dependent power of r. -/
/- Blueprint label(s): eq:PF3
Paper v3: 7.3 [PDF 35]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:PF3"]
def markedModel (g p : ℕ) (Y : ℝ) : ℝ :=
  Real.Gamma (complexity g p) * (4 : ℝ)⁻¹^g / Real.sqrt (Real.pi*complexity g p) *
    (Z Y)⁻¹^(complexity g p) * Real.rpow (r Y) ((p : ℝ)/2) * Real.sqrt (A Y*Theta Y)

/- First degree correction of Lemma 7.2; q counts strictly positive entries. -/
/- Blueprint label(s): lem:first-degree
Paper v3: 7.2 [PDF 35]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:first-degree"]
def degreeCorrection (d : List ℕ) (Y : ℝ) : ℝ :=
  let D : ℝ := d.sum
  let p : ℝ := d.length
  let q : ℝ := (d.filter (fun k => 0 < k)).length
  A Y*(Theta Y*(D^2+(p-4)*D)+2*moment₁ Y*D+q*(q+5-2*p)/2)

/- Endpoint string reduction, Eq.7.13; p fixed but arbitrary. -/
/- Blueprint label(s): eq:PF12
Paper v3: 7.13 [PDF 37]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:PF12"]
theorem endpoint_string (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    let m := dimension g p
    pureC P g (List.replicate p 0 ++ List.replicate m 2) =
      (∏ i ∈ Finset.range p, 5*((m : ℝ)-i) /
        (3*(2*(g : ℝ)-3+p+m-2*i))) * pureC P g (List.replicate (3*g-3) 2) := by
  dsimp only
  have hle : p ≤ dimension g p := by simp only [dimension]; omega
  have hsub : dimension g p-p = 3*g-3 := by simp only [dimension]; omega
  simpa only [hsub] using pureC_zeros_twos_reduce P g p (dimension g p) hg hle

/- Blueprint label(s): eq:PF12
Paper v3: 7.13 [PDF 37]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:PF12"]
theorem endpoint_pure_limit (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      |pureC P g (List.replicate p 0 ++ List.replicate (dimension g p) 2)-1/Real.pi| ≤ C/g := by
  exact HigherOrder.endpoint_pure_limit_proof P p

/- Blueprint label(s): eq:PF13
Paper v3: 7.14 [PDF 37]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:PF13"]
theorem endpoint_ratio (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    ratio P g (List.replicate p 0) y₀ =
      pureC P g (List.replicate p 0 ++ List.replicate (dimension g p) 2) := by
  exact endpoint_normalization P g p hg

end WP
