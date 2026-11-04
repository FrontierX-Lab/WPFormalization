import WPFormalization.HigherOrder.JointBoundaryPair
/-! A zero-constant scalar prefactor uses only strictly lower kernel orders. Its exact finite coefficient convolution preserves the parent degree bound and evaluates to the actual series product; no current-order kernel input is hidden. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open PowerSeries
variable {R : Type*} [CommRing R]

def scalarKernelConvolution {p : ℕ} (n : ℕ) (a : ℕ → R)
    (F : ℕ → MvPolynomial (Fin p) R) : MvPolynomial (Fin p) R :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, MvPolynomial.C (a ij.1) * F ij.2

lemma scalarKernelConvolution_degree {p : ℕ} (n D : ℕ) (a : ℕ → R)
    (F : ℕ → MvPolynomial (Fin p) R) (ha0 : a 0 = 0)
    (hF : ∀ k < n, (F k).totalDegree ≤ D) :
    (scalarKernelConvolution n a F).totalDegree ≤ D := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ij hij
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hj : ij.2 < n
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hF _ hj
  · have hi0 : ij.1 = 0 := by omega
    simp only [hi0, ha0, map_zero, zero_mul, MvPolynomial.totalDegree_zero, Nat.zero_le]

lemma scalarKernelConvolution_eval {p : ℕ} (n : ℕ) (a : ℕ → R)
    (F : ℕ → MvPolynomial (Fin p) R) (ha0 : a 0 = 0)
    (φ : R →+* ℝ) (x : Fin p → ℝ) (f g : Series)
    (hf : ∀ k ≤ n, PowerSeries.coeff k f = φ (a k))
    (hg : ∀ k < n, PowerSeries.coeff k g = MvPolynomial.eval₂ φ x (F k)) :
    PowerSeries.coeff n (f * g) = MvPolynomial.eval₂ φ x (scalarKernelConvolution n a F) := by
  rw [PowerSeries.coeff_mul]
  simp only [scalarKernelConvolution, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hj : ij.2 < n
  · rw [hf ij.1 (by omega), hg ij.2 hj]
  · have hi0 : ij.1 = 0 := by omega
    rw [hi0, hf 0 (by omega), ha0, map_zero, zero_mul, zero_mul]
end WP.HigherOrder.KernelFiniteData
