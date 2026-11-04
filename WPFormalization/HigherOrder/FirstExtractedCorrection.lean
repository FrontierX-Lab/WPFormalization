import WPFormalization.HigherOrder.Extraction
import WPFormalization.HigherOrder.LowOrderAlgebra
import WPFormalization.Volumes.ExtractionPhaseEuler
noncomputable section
namespace WP.HigherOrder
open PowerSeries

lemma gaussianFunctional_add (f g : Polynomial ℝ) :
    gaussianFunctional (f+g)=gaussianFunctional f+gaussianFunctional g := by
  unfold gaussianFunctional
  exact Polynomial.sum_add_index f g _ (by simp) (by intros;ring)
lemma gaussianFunctional_monomial (n : ℕ) (a : ℝ) :
    gaussianFunctional (Polynomial.monomial n a)=a*gaussianMoment n := by
  unfold gaussianFunctional
  exact Polynomial.sum_monomial_index a _ (by simp)
lemma gaussianMoment_six : gaussianMoment 6 = -15 := by
  norm_num [gaussianMoment,Finset.prod_range_succ]

lemma extractionExpPolynomial_one (p : ℕ) (x : ℝ) :
    extractionExpPolynomial p x 1 = extractionLogPolynomial p x 1 := by
  simp [extractionExpPolynomial,Finset.sum_range_succ]
lemma extractionExpPolynomial_two (p : ℕ) (x : ℝ) :
    extractionExpPolynomial p x 2 = extractionLogPolynomial p x 2 +
      Polynomial.C (1/2) * extractionLogPolynomial p x 1 ^ 2 := by
  unfold extractionExpPolynomial
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one]
  norm_num only [PowerSeries.coeff_one,OfNat.ofNat_ne_zero,ite_false,Nat.factorial_zero,
    Nat.factorial_one,Nat.factorial_succ,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
    one_mul,mul_one,PowerSeries.coeff_mk,Polynomial.C_0,Polynomial.C_1,zero_mul,
    one_div,zero_add]
  rw [pow_two,PowerSeries.coeff_mul]
  have hd : Finset.HasAntidiagonal.antidiagonal (2:ℕ) = {(0,2),(1,1),(2,0)} := rfl
  rw [hd]
  simp [extractionLogPolynomial_zero,pow_two]

lemma markedTaylorPolynomial_one (P : PsiTheory) (p : ℕ) (x : ℝ) :
    markedTaylorPolynomial P p x 1 = 0 := by
  simp [markedTaylorPolynomial,euler]
lemma markedTaylorPolynomial_two (P : PsiTheory) (p : ℕ) (x : ℝ) :
    markedTaylorPolynomial P p x 2 = Polynomial.C (markedCoefficient P p 1 (inverseY x)) := by
  have hc : euler (fun _ : ℝ => (1:ℝ)) = fun _ => 0 := by funext t; simp [euler]
  norm_num [markedTaylorPolynomial,Finset.sum_range_succ,Function.iterate_succ_apply',hc,euler]

lemma extractionNumerator_two (P : PsiTheory) (p : ℕ) (x : ℝ) :
    PowerSeries.coeff 2 (extractionNumerator P p x) = markedCoefficient P p 1 (inverseY x) -
      (((euler^[2]) (fun t => Real.log (extractionB p t))) x +
        ((euler (fun t => Real.log (extractionB p t))) x)^2) /
          (2 * (Real.sqrt (euler Psi x))^2) +
      (euler (fun t => Real.log (extractionB p t))) x * ((euler^[3]) extractionS) x /
          (2 * (Real.sqrt (euler Psi x))^4) +
      ((euler^[4]) extractionS) x / (8 * (Real.sqrt (euler Psi x))^4) -
      5 * (((euler^[3]) extractionS) x)^2 / (24 * (Real.sqrt (euler Psi x))^6) := by
  simp only [extractionNumerator,PowerSeries.coeff_mk,Finset.sum_range_succ,
    Finset.sum_range_zero,zero_add,Nat.reduceSub,extractionExpPolynomial_zero,
    markedTaylorPolynomial_zero,markedTaylorPolynomial_one,markedTaylorPolynomial_two,
    extractionExpPolynomial_two,mul_zero,one_mul,mul_one,add_zero]
  rw [gaussianFunctional_add,gaussianFunctional_C]
  norm_num only [extractionLogPolynomial,Nat.reduceAdd,OfNat.ofNat_ne_zero,ite_false,
    Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
    mul_one,Function.iterate_one]
  simp only [pow_two,add_mul,mul_add,Polynomial.monomial_mul_monomial,
    ← Polynomial.monomial_zero_left,gaussianFunctional_add,gaussianFunctional_monomial]
  norm_num [gaussianMoment_six]
  ring
lemma poissonStirlingSeries_one : PowerSeries.coeff 1 poissonStirlingSeries = -(1/12:ℝ) := by
  rw [poissonStirlingSeries,finiteExp_one]
  norm_num [poissonStirlingLog]

lemma extractionDenominator_one (x : ℝ) :
    PowerSeries.coeff 1 (extractionDenominator x) = 0 := by
  norm_num [extractionDenominator]
lemma extractionDenominator_two (x : ℝ) :
    PowerSeries.coeff 2 (extractionDenominator x) = -(1/(12*Psi x)) := by
  norm_num [extractionDenominator,poissonStirlingSeries_one]
  ring

lemma rawExtractedCoefficient_one_algebra (P : PsiTheory) (p : ℕ) (Y : ℝ) :
    rawExtractedCoefficient P p 1 Y =
      PowerSeries.coeff 2 (extractionNumerator P p (XR Y)) + 1/(12*Psi (XR Y)) := by
  unfold rawExtractedCoefficient
  norm_num only [Nat.mul_one]
  rw [coeff_two_mul,coeff_one_inv_unit _ (extractionDenominator_constant _),
    coeff_two_inv_unit _ (extractionDenominator_constant _),
    extractionDenominator_one,extractionNumerator_constant]
  simp only [PowerSeries.constantCoeff_inv,extractionDenominator_constant,inv_one,mul_one,
    sq,mul_zero,one_mul,zero_sub]
  rw [extractionDenominator_two]
  ring

lemma iteratedEuler_congr_germ {f g : ℝ → ℝ} {x : ℝ}
    (h : f =ᶠ[nhds x] g) (n : ℕ) :
    ((euler^[n]) f) =ᶠ[nhds x] ((euler^[n]) g) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact Filter.EventuallyEq.fun_mul Filter.EventuallyEq.rfl ih.deriv

lemma extractionS_iteratedEuler_eq (x : ℝ) (hx : x ∈ Set.Ioo (0:ℝ) xCritical) (n : ℕ) :
    ((euler^[n+1]) extractionS) x = ((euler^[n]) Psi) x := by
  have hg : euler extractionS =ᶠ[nhds x] Psi := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact WP.Analysis.extractionS_euler_eq_Psi t ht
  rw [Function.iterate_succ_apply]
  exact (iteratedEuler_congr_germ hg n).eq_of_nhds

/- D.24, obtained by evaluating the ORIGINAL CG3 finite polynomial in degree two.
The identity is asserted on its original initial domain; endpoint removal follows
from the independently proved common extension in Theorem 10.2. -/
@[blueprint "eq:CG12"]
theorem first_extracted_correction (P : PsiTheory) (p : ℕ)
    (Y : ℝ) (hY : Y ∈ Set.Ioo (0:ℝ) y₀) :
    extractedCoefficient P p 1 Y = markedCoefficient P p 1 Y -
      (((euler^[2]) (fun t => Real.log (extractionB p t))) (XR Y) +
        ((euler (fun t => Real.log (extractionB p t))) (XR Y))^2) /
          (2 * euler Psi (XR Y)) +
      (euler (fun t => Real.log (extractionB p t))) (XR Y) * ((euler^[2]) Psi) (XR Y) /
          (2 * (euler Psi (XR Y))^2) +
      ((euler^[3]) Psi) (XR Y) / (8 * (euler Psi (XR Y))^2) -
      5 * (((euler^[2]) Psi) (XR Y))^2 / (24 * (euler Psi (XR Y))^3) +
      1/(12*Psi (XR Y)) := by
  have hx : XR Y ∈ Set.Ioo (0:ℝ) xCritical := by
    constructor
    · simpa only [XR_zero] using
        XR_strictMonoOn (show (0:ℝ) ∈ Set.Iic y₀ from y₀_pos.le)
          hY.2.le hY.1
    · exact XR_strictMonoOn hY.2.le (le_refl y₀) hY.2
  have hi : inverseY (XR Y) = Y := WP.Analysis.inverseY_eq_of_root (XR Y) Y hY.2.le rfl
  have hv : 0 < euler Psi (XR Y) :=
    mul_pos hx.1 (WP.Analysis.Psi_deriv_pos_interior _ ⟨hx.1.le,hx.2⟩)
  have hs2 : Real.sqrt (euler Psi (XR Y))^2 = euler Psi (XR Y) := Real.sq_sqrt hv.le
  have hs4 : Real.sqrt (euler Psi (XR Y))^4 = (euler Psi (XR Y))^2 := by
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,hs2]
  have hs6 : Real.sqrt (euler Psi (XR Y))^6 = (euler Psi (XR Y))^3 := by
    rw [show (6:ℕ)=2*3 by norm_num,pow_mul,hs2]
  rw [extractedCoefficient,ite_eq_right (ne_of_gt hY.1),ite_eq_right (ne_of_lt hY.2),
    rawExtractedCoefficient_one_algebra,extractionNumerator_two,hi,
    extractionS_iteratedEuler_eq _ hx 2,extractionS_iteratedEuler_eq _ hx 3,hs2,hs4,hs6]

end WP.HigherOrder
