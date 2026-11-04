import WPFormalization.HigherOrder.JetLocality
import WPFormalization.Analysis.KernelJets
import WPFormalization.Analysis.KernelMomentBounds
import Mathlib
/-! The actual inverse Taylor coefficients are explicit polynomials in a finite unit theta prefix. The construction uses invOfUnit over a multivariate polynomial ring and has total degree at most the coefficient index. The physical restriction includes the genuine critical normalized kernel. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open Set PowerSeries
abbrev ThetaPolynomial (N : ℕ) := MvPolynomial (Fin (N + 1)) ℝ

def unitThetaTemplate (N : ℕ) : PowerSeries (ThetaPolynomial N) :=
  PowerSeries.mk (fun n => if n = 0 then 1 else if hn : n ≤ N then MvPolynomial.X ⟨n, by omega⟩ else 0)

@[simp] lemma unitThetaTemplate_constant (N : ℕ) :
    PowerSeries.constantCoeff (unitThetaTemplate N) = 1 := by
  simp [unitThetaTemplate, ← PowerSeries.coeff_zero_eq_constantCoeff]

lemma unitThetaTemplate_degree (N n : ℕ) :
    (PowerSeries.coeff n (unitThetaTemplate N)).totalDegree ≤ n := by
  simp only [unitThetaTemplate, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst n
    simp
  · by_cases hN : n ≤ N
    · simp only [ite_eq_right hn, dite_eq_left hN, MvPolynomial.totalDegree_X]
      omega
    · simp [hn, hN]

def kernelCoefficientRecipe (N n : ℕ) : ThetaPolynomial N :=
  PowerSeries.coeff n (PowerSeries.invOfUnit (unitThetaTemplate N) 1)

lemma kernelCoefficientRecipe_degree (N n : ℕ) :
    (kernelCoefficientRecipe N n).totalDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [kernelCoefficientRecipe, PowerSeries.coeff_zero_eq_constantCoeff]
    rw [kernelCoefficientRecipe, PowerSeries.coeff_invOfUnit, ite_eq_right hn]
    simp only [inv_one, Units.val_one, neg_one_mul]
    rw [MvPolynomial.totalDegree_neg]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro ij hij
    by_cases ht : ij.2 < n
    · rw [ite_eq_left ht]
      apply (MvPolynomial.totalDegree_mul _ _).trans
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hprevious := ih ij.2 ht
      change (PowerSeries.coeff ij.2 (PowerSeries.invOfUnit (unitThetaTemplate N) 1)).totalDegree ≤ ij.2 at hprevious
      exact (add_le_add (unitThetaTemplate_degree N ij.1) hprevious).trans_eq hsum
    · rw [ite_eq_right ht]
      simp

lemma thetaTaylor_inv_eq_kernelTaylor (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
    (Analysis.realTaylor (fun z : ℂ => (barK Y z)⁻¹))⁻¹ = Analysis.realTaylor (barK Y) := by
  have ha := (barK_differentiable Y).analyticAt 0
  have h0 : barK Y 0 ≠ 0 := by rw [barK_zero_closed Y hY]; norm_num
  have he := Analysis.realTaylor_inv (f := fun z : ℂ => (barK Y z)⁻¹) (ha.inv h0) (inv_ne_zero h0)
    (Analysis.realCoefficients_inv ha h0 (barK_realCoefficients Y))
  simpa only [Pi.inv_apply, inv_inv] using he.symm

lemma kernelCoefficientRecipe_eval (N n : ℕ) (hn : n ≤ N) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
    MvPolynomial.eval (fun i : Fin (N + 1) => theta Y i.val) (kernelCoefficientRecipe N n) =
      realCoeff (barK Y) n := by
  let φ : ThetaPolynomial N →+* ℝ := MvPolynomial.eval (fun i : Fin (N + 1) => theta Y i.val)
  let f := unitThetaTemplate N
  have hf0 : PowerSeries.constantCoeff f = 1 := unitThetaTemplate_constant N
  have hmap0 : PowerSeries.constantCoeff (PowerSeries.map φ f) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hf0, map_one]
  have hmapinv : PowerSeries.map φ (PowerSeries.invOfUnit f 1) = (PowerSeries.map φ f)⁻¹ := by
    apply (PowerSeries.eq_inv_iff_mul_eq_one (by rw [hmap0]; exact one_ne_zero)).mpr
    rw [← map_mul, PowerSeries.invOfUnit_mul f 1 (by simpa using hf0), map_one]
  have hagree : AgreeBelow (N + 1) (PowerSeries.map φ f)
      (Analysis.realTaylor (fun z : ℂ => (barK Y z)⁻¹)) := by
    intro k hk
    rw [PowerSeries.coeff_map, Analysis.realTaylor_coeff]
    dsimp only [f]
    change φ (PowerSeries.coeff k (unitThetaTemplate N)) = theta Y k
    simp only [unitThetaTemplate, PowerSeries.coeff_mk]
    by_cases hk0 : k = 0
    · subst k
      simp only [ite_true, map_one]
      exact (Analysis.theta_zero_closed Y hY).symm
    · have hkN : k ≤ N := by omega
      simp only [ite_eq_right hk0, dite_eq_left hkN, φ, MvPolynomial.eval_X]
  have hi := hagree.inv n (by omega)
  rw [← hmapinv, thetaTaylor_inv_eq_kernelTaylor Y hY] at hi
  simpa only [PowerSeries.coeff_map, Analysis.realTaylor_coeff, f, kernelCoefficientRecipe, φ] using hi
end WP.HigherOrder.KernelFiniteData
