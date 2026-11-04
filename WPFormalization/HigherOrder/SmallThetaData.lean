import WPFormalization.HigherOrder.FiniteThetaInverse
import WPFormalization.Intersection.CanonicalBackground
import WPFormalization.Intersection.ShiftedRecursion
import WPFormalization.HigherOrder.Triangular
/-! The actual bounded-complexity amplitude is an explicit polynomial in the finite theta prefix. Its total degree is at most the actual deficit. The genuine finite background formula, instability/dimension conventions and critical endpoint are retained. No coefficientwise positivity is asserted here. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open Set

def finiteSmallThetaPolynomial (P : PsiTheory) (g : ℕ) (d : List ℕ) (N B m : ℕ) : ThetaPolynomial N :=
  MvPolynomial.C ((4 : ℝ) ^ g * doubleWeight (d.map Int.ofNat)) *
    ∑ l ∈ backgroundVectors N B m,
      MvPolynomial.C (P.psi g (d.map Int.ofNat ++ (backgroundDegrees l).map Int.ofNat)) *
      ∏ i : Fin N,
        (MvPolynomial.C (-(oddFactorial (i.val + 1) : ℝ)) * kernelCoefficientRecipe N (i.val + 1)) ^ (l i) *
          MvPolynomial.C (((l i).factorial : ℝ)⁻¹)

lemma finiteSmallThetaPolynomial_degree (P : PsiTheory) (g : ℕ) (d : List ℕ) (N B m : ℕ) :
    (finiteSmallThetaPolynomial P g d N B m).totalDegree ≤ m := by
  unfold finiteSmallThetaPolynomial
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro l hl
  have hdim : backgroundDegree l = m := (Finset.mem_filter.mp hl).2
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  apply (Finset.sum_le_sum (fun i hi => ?_)).trans (le_of_eq hdim)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, add_zero]
  apply (MvPolynomial.totalDegree_pow _ _).trans
  have hbase : (MvPolynomial.C (-(oddFactorial (i.val + 1) : ℝ)) * kernelCoefficientRecipe N (i.val + 1)).totalDegree ≤ i.val + 1 := by
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simpa only [MvPolynomial.totalDegree_C, zero_add] using kernelCoefficientRecipe_degree N (i.val + 1)
  exact (Nat.mul_le_mul_left (l i) hbase).trans_eq (Nat.mul_comm _ _)

lemma finiteSmallThetaPolynomial_eval (P : PsiTheory) (g : ℕ) (d : List ℕ) (N B m : ℕ)
    (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
    MvPolynomial.eval (fun i : Fin (N + 1) => theta Y i.val) (finiteSmallThetaPolynomial P g d N B m) =
      (4 : ℝ) ^ g * finiteBackgroundAmplitude P g (d.map Int.ofNat) B m
        (fun i : Fin N => normalizedBackgroundTime Y i.val) := by
  simp only [finiteSmallThetaPolynomial, map_mul, map_sum, map_prod, map_pow, MvPolynomial.eval_C]
  have hpoly (i : Fin N) :
      MvPolynomial.eval (fun i : Fin (N + 1) => theta Y i.val) (kernelCoefficientRecipe N (i.val + 1)) =
        realCoeff (barK Y) (i.val + 1) := kernelCoefficientRecipe_eval N (i.val + 1) (by omega) Y hY
  simp_rw [hpoly]
  simp [finiteBackgroundAmplitude, normalizedBackgroundTime, div_eq_mul_inv, mul_assoc]

lemma smallW_polynomial_in_finite_theta_data (P : PsiTheory) (K g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hp : 1 ≤ d.length) (hK : complexity g d.length ≤ K) :
    ∃ F : MvPolynomial (Fin ((3 * K) / 2 + 2)) ℝ, F.totalDegree ≤ deficit g d ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀,
        smallW P Y g d = MvPolynomial.eval (fun i : Fin ((3 * K) / 2 + 2) => theta Y i.val) F := by
  have hm : deficit g d ≤ (3 * K) / 2 := by unfold deficit dimension complexity Stable at *; omega
  by_cases hd : d.sum ≤ dimension g d.length
  · refine ⟨finiteSmallThetaPolynomial P g d ((3 * K) / 2 + 1) (deficit g d) (deficit g d),
      finiteSmallThetaPolynomial_degree _ _ _ _ _ _, ?_⟩
    intro Y hY
    rw [finiteSmallThetaPolynomial_eval P g d _ _ _ Y hY,
      finiteBackgroundAmplitude_normalized_canonical P g d Y hY hs hd _ _ (by omega) (by omega) le_rfl]
    rfl
  · refine ⟨0, by simp, ?_⟩
    intro Y hY
    simp [smallW, normalized_excess P g d Y (by omega)]
end WP.HigherOrder.KernelFiniteData
