import WPFormalization.HigherOrder.AffineShiftMoment
import WPFormalization.HigherOrder.FiniteKernelConvolution
/-! Actual scalar front factors have literal finite coefficient recipes. Their zero constant is fixed algebraically and preserves the strict loss: coefficient n uses scalar inputs only below n. Integer shifts, the genuine shiftVariable and finite products are identified directly, without asymptotic assumptions. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open PowerSeries
open JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def scalarShiftRecipe (s : ℤ) (a : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (n + 1), (integerShiftWeight s n i : R) * a i

lemma scalarShiftRecipe_eval (s : ℤ) (a : ℕ → R) (n : ℕ) (φ : R →+* ℝ)
    (f : Series) (ha : ∀ i ≤ n, PowerSeries.coeff i f = φ (a i)) :
    PowerSeries.coeff n (complexityShift (s : ℝ) f) = φ (scalarShiftRecipe s a n) := by
  rw [complexityShift_coeff_integer_weights]
  simp only [scalarShiftRecipe, map_sum, map_mul, map_intCast]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ha i (by have := Finset.mem_range.mp hi; omega)]

def shiftVariableIntegerWeight (n : ℕ) : ℤ := if n = 0 then 0 else 1

lemma shiftVariable_coeff_integer (n : ℕ) :
    PowerSeries.coeff n (shiftVariable 1) = (shiftVariableIntegerWeight n : ℝ) := by
  cases n with
  | zero => simp [shiftVariableIntegerWeight, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    have hs := PowerSeries.coeff_X_pow_mul ((1 - C 1 * PowerSeries.X : Series)⁻¹) 1 n
    have hi := inverse_linear_pow_coeff 1 1 n (by omega)
    simp only [pow_one] at hs hi
    have hchoose : 1 + n - 1 = n := by omega
    simpa [shiftVariable, shiftVariableIntegerWeight, hchoose] using hs.trans hi

def linearFrontRecipe (A : R) (a : ℕ → R) (n : ℕ) : R :=
  A * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
    (shiftVariableIntegerWeight ij.1 : R) * scalarShiftRecipe 1 a ij.2

lemma linearFrontRecipe_zero (A : R) (a : ℕ → R) : linearFrontRecipe A a 0 = 0 := by
  simp [linearFrontRecipe, shiftVariableIntegerWeight]

lemma linearFrontRecipe_eval (A : R) (a : ℕ → R) (n : ℕ) (φ : R →+* ℝ)
    (f : Series) (ha : ∀ i < n, PowerSeries.coeff i f = φ (a i)) :
    PowerSeries.coeff n (C (φ A) * shiftVariable 1 * complexityShift 1 f) =
      φ (linearFrontRecipe A a n) := by
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul]
  simp only [linearFrontRecipe, map_mul, map_sum, map_intCast]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hi : ij.1 = 0
  · rw [hi, shiftVariable_coeff_integer]
    simp only [shiftVariableIntegerWeight, ite_true, Int.cast_zero, zero_mul]
  · rw [shiftVariable_coeff_integer]
    congr 1
    simpa only [Int.cast_one] using scalarShiftRecipe_eval 1 a ij.2 φ f (by
      intro i hi'
      exact ha i (by omega))

def scalarProductRecipe (a b : ℕ → R) (n : ℕ) : R :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a ij.1 * b ij.2

lemma scalarProductRecipe_eval (a b : ℕ → R) (n : ℕ) (φ : R →+* ℝ)
    (f g : Series) (ha0 : a 0 = 0)
    (ha : ∀ i ≤ n, PowerSeries.coeff i f = φ (a i))
    (hb : ∀ i < n, PowerSeries.coeff i g = φ (b i)) :
    PowerSeries.coeff n (f * g) = φ (scalarProductRecipe a b n) := by
  rw [PowerSeries.coeff_mul]
  simp only [scalarProductRecipe, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hj : ij.2 < n
  · rw [ha ij.1 (by omega), hb ij.2 hj]
  · have hi0 : ij.1 = 0 := by omega
    rw [hi0, ha 0 (by omega), ha0, map_zero, zero_mul, zero_mul]

lemma scalarProductRecipe_zero (a b : ℕ → R) (ha0 : a 0 = 0) :
    scalarProductRecipe a b 0 = 0 := by simp [scalarProductRecipe, ha0]
end WP.HigherOrder.KernelFiniteData
