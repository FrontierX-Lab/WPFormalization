import WPFormalization.External.IntersectionEstimates
import WPFormalization.Intersection.CriticalCoefficient
import WPFormalization.Intersection.PrimitiveNormalized
/-! Actual one- and two-point estimates used in Appendix B. The one-point
closed formula and two-point comparison are the registered deferred classical
inputs. The uniform bound itself is proved by an elementary rational
supersolution of the exact one-point recurrence, avoiding any new asymptotic
assumption. These theorems do not assert the general primitive bound. -/
noncomputable section
namespace WP
def pointEdgeMajorant (x : ℝ) : ℝ := 8/25-4/(5*(18*x+1))
lemma pointEdgeMajorant_initial : (5/18 : ℝ) ≤ pointEdgeMajorant 1 := by
  norm_num [pointEdgeMajorant]
lemma pointEdgeMajorant_lt (x : ℝ) (hx : 1 ≤ x) : pointEdgeMajorant x < 8/25 := by
  have hp : 0 < 18*x+1 := by linarith
  have hf : 0 < (4 : ℝ)/(5*(18*x+1)) := by positivity
  unfold pointEdgeMajorant
  linarith
lemma pointEdgeMajorant_step (x : ℝ) (hx : 1 ≤ x) :
    (1+5/(36*x*(x+1)))*pointEdgeMajorant x < pointEdgeMajorant (x+1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x+1 := by linarith
  have hp1 : 0 < 18*x+1 := by linarith
  have hp19 : 0 < 18*x+19 := by linarith
  have he : pointEdgeMajorant (x+1)-(1+5/(36*x*(x+1)))*pointEdgeMajorant x =
      (6*x+19)/(15*x*(x+1)*(18*x+1)*(18*x+19)) := by
    unfold pointEdgeMajorant
    rw [show 18*(x+1)+1 = 18*x+19 by ring]
    field_simp [hx0.ne', hx1.ne', hp1.ne', hp19.ne']
    <;> ring
  have hf : 0 < (6*x+19)/(15*x*(x+1)*(18*x+1)*(18*x+19)) := by positivity
  linarith
/-- The actual one-zero two-point number, rather than an abstract recurrence sequence. -/
def pointEdge (P : PsiTheory) (g : ℕ) : ℝ := pureC P g [0,3*g-1]
lemma pure_one_zero_one_point (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g) :
    pure P g [0,3*g-1] = pure P g [3*g-2] := by
  have hs := P.string g [((3*g-1 : ℕ) : ℤ)] (by simp only [Stable, List.length_cons, List.length_nil]; omega)
  norm_num [Finset.sum_range_succ] at hs
  have hi : ((3*g-1 : ℕ) : ℤ)-1 = ((3*g-2 : ℕ) : ℤ) := by omega
  rw [hi] at hs
  simpa only [pure, List.map_cons, List.map_nil, Int.ofNat_eq_natCast, Nat.cast_zero] using hs
lemma pointEdge_formula (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g) :
    pointEdge P g = (4 : ℝ)^g*(oddFactorial (3*g-1) : ℝ)/
      (3^(2*g)*Real.Gamma (2*g : ℕ)) * (1/((24 : ℝ)^g*g.factorial)) := by
  unfold pointEdge pureC
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  rw [show oddFactorial 0 = 1 from by decide,
    show complexity g (0+1+1) = 2*g by unfold complexity; omega]
  simp only [Nat.cast_one, one_mul, mul_one]
  rw [pure_one_zero_one_point P g hg, one_point P g hg]
lemma pointEdge_initial (P : PsiTheory) : pointEdge P 1 = 5/18 := by
  norm_num [pointEdge, pureC, pure, complexity, oddFactorial,
    Finset.prod_range_succ, psi_1_0_2]
lemma pointEdge_step (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g) :
    pointEdge P (g+1) = (1+5/(36*(g : ℝ)*(g+1)))*pointEdge P g := by
  rw [pointEdge_formula P (g+1) (by omega), pointEdge_formula P g hg]
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hodd : 3*(g+1)-1 = ((3*g-1)+1+1)+1 := by omega
  rw [hodd, oddFactorial_succ, oddFactorial_succ, oddFactorial_succ]
  have hgamma : Real.Gamma (2*(g+1) : ℕ) =
      (2*(g : ℝ))*(2*(g : ℝ)+1)*Real.Gamma (2*g : ℕ) := by
    rw [show 2*(g+1) = 2*g+2 by omega,
      ← gamma_mul_ascFactorial (2*g) 2 (by omega)]
    norm_num [Nat.ascFactorial_succ]
    ring
  have hpow : (3 : ℝ)^(2*(g+1)) = 3^(2*g)*9 := by
    rw [show 2*(g+1) = 2*g+2 by omega, pow_add]
    norm_num
  rw [hgamma, hpow, Nat.factorial_succ, pow_succ, pow_succ]
  have hidx : ((3*g-1 : ℕ) : ℝ) = 3*(g : ℝ)-1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  push_cast
  rw [hidx]
  have hg0 : (g : ℝ) ≠ 0 := by linarith
  have hgs : (g : ℝ)+1 ≠ 0 := by linarith
  have h2g1 : 2*(g : ℝ)+1 ≠ 0 := by linarith
  have hG : Real.Gamma (2*(g : ℝ)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hfact : (g.factorial : ℝ) ≠ 0 := by exact_mod_cast g.factorial_ne_zero
  field_simp [hg0, hgs, h2g1, hG, hfact]
  <;> ring
lemma pointEdge_le_majorant (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g) :
    pointEdge P g ≤ pointEdgeMajorant g := by
  induction g, hg using Nat.le_induction with
  | base => rw [pointEdge_initial]; simpa only [Nat.cast_one] using pointEdgeMajorant_initial
  | succ g hg ih =>
    rw [pointEdge_step P g hg]
    have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
    have hc : 0 ≤ 1+5/(36*(g : ℝ)*(g+1)) := by positivity
    have hs := pointEdgeMajorant_step g hgR
    push_cast
    exact le_trans (mul_le_mul_of_nonneg_left ih hc) hs.le
lemma pointEdge_lt (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g) :
    pointEdge P g < 8/25 :=
  (pointEdge_le_majorant P g hg).trans_lt
    (pointEdgeMajorant_lt g (by exact_mod_cast hg))
lemma pureC_two_point_lt (P : PsiTheory) (g d₁ d₂ : ℕ) (hg : 1 ≤ g)
    (hd : d₁+d₂ = 3*g-1) : pureC P g [d₁,d₂] < 8/25 :=
  (two_point P g d₁ d₂ hg hd).trans_lt (pointEdge_lt P g hg)
lemma pureC_one_point_edge (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g) :
    pureC P g [3*g-2] = ((6*(g : ℝ)-3)/(6*g-1))*pointEdge P g := by
  unfold pointEdge pureC
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  rw [pure_one_zero_one_point P g hg]
  have hc₁ : complexity g (0+1) = 2*g-1 := by unfold complexity; omega
  have hc₂ : complexity g (0+1+1) = (2*g-1)+1 := by unfold complexity; omega
  rw [hc₁, hc₂, pow_succ]
  have hp : (0 : ℝ) < (2*g-1 : ℕ) := by exact_mod_cast (show 0 < 2*g-1 by omega)
  rw [Nat.cast_add, Nat.cast_one, Real.Gamma_add_one hp.ne']
  have ho : 3*g-1 = (3*g-2)+1 := by omega
  rw [ho, oddFactorial_succ]
  rw [show oddFactorial 0 = 1 by decide]
  simp only [Nat.cast_one, one_mul]
  have h3 : ((3*g-2 : ℕ) : ℝ) = 3*(g : ℝ)-2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : ((2*g-1 : ℕ) : ℝ) = 2*(g : ℝ)-1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  push_cast
  rw [h3,h2]
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hG : Real.Gamma (2*(g : ℝ)-1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp [hG, show 2*(g : ℝ)-1 ≠ 0 by linarith, show 6*(g : ℝ)-1 ≠ 0 by linarith]
  <;> ring_nf
  field_simp [show -1+(g : ℝ)*6 ≠ 0 by linarith]
  <;> ring
lemma pureC_one_point_lt (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g) :
    pureC P g [3*g-2] < 8/25 := by
  rw [pureC_one_point_edge P g hg]
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hc : (6*(g : ℝ)-3)/(6*g-1) ≤ 1 := by
    apply (div_le_one (by linarith : 0 < 6*(g : ℝ)-1)).mpr
    linarith
  calc
    _ ≤ 1*pointEdge P g := mul_le_mul_of_nonneg_right hc (pureC_nonneg P g _)
    _ < 8/25 := by simpa using pointEdge_lt P g hg
end WP
