import WPFormalization.HigherOrder.JointBoundaryHead
import WPFormalization.HigherOrder.FirstScalarCoefficients
import WPFormalization.HigherOrder.ShiftExtraction
/-! Exact canonical cusp coefficients as literal finite-data recipes. Current actual joint profile-stratum certificates through K, finitely many true dilaton moments, low dilaton coefficients and inverse A supply the fixed-shift dilaton coefficient. The all-order profile certificates remain an explicit inductive input, not a new external result. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
open Set PowerSeries
variable {R : Type*} [CommRing R] [Algebra ℝ R]

def shiftCoefficient (K i : ℕ) : ℝ :=
  PowerSeries.coeff (K - i) (((1 - C (-1) * PowerSeries.X : Series)⁻¹) ^ i)

def cuspMomentRecipe (p K b D : ℕ)
    (F : ℕ → (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R)
    (M W : ℕ → R) (Ai : R) : R :=
  Ai * ∑ i ∈ Finset.range (K + 1),
    algebraMap ℝ R (shiftCoefficient K i) *
      headMomentRecipe b D (F i) (fun _ : Fin p => 0) M W

lemma actual_cusp_moment_recipe (P : PsiTheory) (p K b D : ℕ)
    (F : ℕ → (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R)
    (hdegree : ∀ i ≤ K, ∀ σ, (F i σ).totalDegree ≤ D)
    (φ : ℝ → R →ₐ[ℝ] ℝ)
    (hactual : ∀ i ≤ K, ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (p + 1) → ℕ,
      profileCoefficient P Y (List.ofFn d) i =
        MvPolynomial.eval₂ (φ Y).toRingHom (fun k => (d k : ℝ))
          (F i (classify (p + 1) b d)))
    (M W : ℕ → R) (Ai : R)
    (hm : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D →
      HasSum (fun n : ℕ => (n : ℝ) ^ k * canonicalDilatonCoefficient Y n) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ n : ℕ, n < b + 1 →
      canonicalDilatonCoefficient Y n = (φ Y) (W n))
    (hAi : ∀ Y ∈ Icc (0 : ℝ) y₀, (φ Y) Ai = (A Y)⁻¹) :
    ∀ Y ∈ Icc (0 : ℝ) y₀,
      cuspCoefficient P Y p K = (φ Y) (cuspMomentRecipe p K b D F M W Ai) := by
  intro Y hY
  have hhead (i : ℕ) (hi : i ≤ K) :
      HasSum (fun n : ℕ => canonicalDilatonCoefficient Y n *
        profileCoefficient P Y (n :: List.replicate p 0) i)
        ((φ Y) (headMomentRecipe b D (F i) (fun _ : Fin p => 0) M W)) := by
    have hh := actual_profile_head_moment_recipe P p i b D (F i) (hdegree i hi)
      (fun Z => (φ Z).toRingHom) (hactual i hi) (fun _ : Fin p => 0) M W
      canonicalDilatonCoefficient hm hw Y hY
    simpa only [List.ofFn_const, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hh
  have hsum := hasSum_sum (s := Finset.range (K + 1)) (fun i hi =>
    (hhead i (by have := Finset.mem_range.mp hi; omega)).mul_right (shiftCoefficient K i))
  have hs : HasSum (fun n : ℕ => canonicalDilatonCoefficient Y n *
      PowerSeries.coeff K (complexityShift (-1)
        (formalProfile P Y (n :: List.replicate p 0))))
      ((φ Y) (∑ i ∈ Finset.range (K + 1),
        algebraMap ℝ R (shiftCoefficient K i) *
          headMomentRecipe b D (F i) (fun _ : Fin p => 0) M W)) := by
    convert! hsum using 1
    · funext n
      rw [complexityShift_coeff_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [formalProfile, PowerSeries.coeff_mk, shiftCoefficient]
      ring
    · simp only [map_sum, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  have hsucc : HasSum (fun n : ℕ => canonicalDilatonCoefficient Y (n + 1) *
      PowerSeries.coeff K (complexityShift (-1)
        (formalProfile P Y ((n + 1) :: List.replicate p 0))))
      ((φ Y) (∑ i ∈ Finset.range (K + 1),
        algebraMap ℝ R (shiftCoefficient K i) *
          headMomentRecipe b D (F i) (fun _ : Fin p => 0) M W)) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => canonicalDilatonCoefficient Y n *
      PowerSeries.coeff K (complexityShift (-1)
        (formalProfile P Y (n :: List.replicate p 0)))) 1).mpr
    simpa [Finset.sum_range_one, canonicalDilatonCoefficient] using hs
  have hc : cuspCoefficient P Y p K =
      (A Y)⁻¹ * ∑' n : ℕ, canonicalDilatonCoefficient Y (n + 1) *
        PowerSeries.coeff K (complexityShift (-1)
          (formalProfile P Y ((n + 1) :: List.replicate p 0))) := by
    have he := congrArg (fun f : Series => PowerSeries.coeff K f) (formalCusp_recursion P Y hY p)
    simpa only [formalCusp, PowerSeries.coeff_mk, cuspSeries, PowerSeries.coeff_C_mul,
      coefficientSum_coeff, bCoeff_eq_canonicalDilatonCoefficient] using he
  rw [hc, hsucc.tsum_eq]
  simp only [cuspMomentRecipe, map_mul, hAi Y hY]
end WP.HigherOrder.JointBoundary
