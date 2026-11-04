import WPFormalization.HigherOrder.FiniteThetaInverse
/-! Literal finite-data recipes for unit-series inversion. The template fixes its constant coefficient to one algebraically. Evaluation agrees with the actual inverse through the requested finite order; neither convergence nor division by a polynomial-valued constant is assumed. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open PowerSeries

lemma kernelCoefficientRecipe_eval_unit (N n : ℕ) (hn : n ≤ N) (f : Series)
    (hf0 : PowerSeries.constantCoeff f = 1) :
    MvPolynomial.eval (fun i : Fin (N + 1) => PowerSeries.coeff i.val f)
      (kernelCoefficientRecipe N n) = PowerSeries.coeff n f⁻¹ := by
  let φ : ThetaPolynomial N →+* ℝ :=
    MvPolynomial.eval (fun i : Fin (N + 1) => PowerSeries.coeff i.val f)
  let t := unitThetaTemplate N
  have ht0 : PowerSeries.constantCoeff t = 1 := unitThetaTemplate_constant N
  have hmap0 : PowerSeries.constantCoeff (PowerSeries.map φ t) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, ht0, map_one]
  have hmapinv : PowerSeries.map φ (PowerSeries.invOfUnit t 1) = (PowerSeries.map φ t)⁻¹ := by
    apply (PowerSeries.eq_inv_iff_mul_eq_one (by rw [hmap0]; exact one_ne_zero)).mpr
    rw [← map_mul, PowerSeries.invOfUnit_mul t 1 (by simpa using ht0), map_one]
  have hagree : AgreeBelow (N + 1) (PowerSeries.map φ t) f := by
    intro k hk
    rw [PowerSeries.coeff_map]
    dsimp only [t]
    simp only [unitThetaTemplate, PowerSeries.coeff_mk]
    by_cases hk0 : k = 0
    · subst k
      simp only [ite_true, map_one]
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hf0.symm
    · have hkN : k ≤ N := by omega
      simp only [ite_eq_right hk0, dite_eq_left hkN, φ, MvPolynomial.eval_X]
  have hi := hagree.inv n (by omega)
  rw [← hmapinv] at hi
  simpa only [PowerSeries.coeff_map, t, kernelCoefficientRecipe, φ] using hi

variable {R : Type*} [CommRing R] [Algebra ℝ R]

def unitInverseRecipe (N n : ℕ) (a : ℕ → R) : R :=
  MvPolynomial.eval₂ (algebraMap ℝ R) (fun i : Fin (N + 1) => a i.val)
    (kernelCoefficientRecipe N n)

lemma unitInverseRecipe_eval (N n : ℕ) (hn : n ≤ N) (a : ℕ → R)
    (φ : R →ₐ[ℝ] ℝ) (f : Series) (hf0 : PowerSeries.constantCoeff f = 1)
    (ha : ∀ k ≤ N, φ (a k) = PowerSeries.coeff k f) :
    φ (unitInverseRecipe N n a) = PowerSeries.coeff n f⁻¹ := by
  have he := MvPolynomial.eval₂_comp_left φ.toRingHom (algebraMap ℝ R)
    (fun i : Fin (N + 1) => a i.val) (kernelCoefficientRecipe N n)
  have hc : φ.toRingHom.comp (algebraMap ℝ R) = RingHom.id ℝ := by
    ext x
    exact φ.commutes x
  have hx : (φ.toRingHom ∘ fun i : Fin (N + 1) => a i.val) =
      (fun i : Fin (N + 1) => PowerSeries.coeff i.val f) := by
    funext i
    exact ha i.val (by omega)
  have hmap : φ (unitInverseRecipe N n a) =
      MvPolynomial.eval (fun i : Fin (N + 1) => PowerSeries.coeff i.val f)
        (kernelCoefficientRecipe N n) := by
    change φ.toRingHom (MvPolynomial.eval₂ (algebraMap ℝ R)
        (fun i : Fin (N + 1) => a i.val) (kernelCoefficientRecipe N n)) =
      MvPolynomial.eval₂ (RingHom.id ℝ)
        (fun i : Fin (N + 1) => PowerSeries.coeff i.val f) (kernelCoefficientRecipe N n)
    simpa only [hc, hx] using he
  exact hmap.trans (kernelCoefficientRecipe_eval_unit N n hn f hf0)
end WP.HigherOrder.KernelFiniteData
