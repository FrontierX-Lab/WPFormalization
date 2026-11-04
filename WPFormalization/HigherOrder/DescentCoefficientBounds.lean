import WPFormalization.HigherOrder.InverseCuspBounds
import WPFormalization.HigherOrder.LargeWeightRemainder
import WPFormalization.HigherOrder.ComplexCuspMajorant
import WPFormalization.HigherOrder.ShiftExtraction
/-! Uniform true C.4 coefficient data for the one-marking descent. The actual fixed-path genus, shifted genus, cusp, and inverse cusp factors have common exponential coefficient constants. This coefficient theorem does not assume or assert C.3 remainders. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries Set
lemma exp_geometric_convolution_bound (C B : ℝ) (hC : 0 ≤ C) (hB : 1 ≤ B) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.exp ℝ) * PowerSeries.mk (fun i => C * B ^ i)) ≤
      2 * C * (2 * B) ^ n := by
  rw [exp_series_convolution_coeff]
  have hB0 : 0 ≤ B := by linarith
  have hterm (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      C * B ^ i / ((n - i).factorial : ℝ) ≤ C * B ^ n := by
    have hi' : i ≤ n := by have ht := Finset.mem_range.mp hi; omega
    have hfac : (1 : ℝ) ≤ (n - i).factorial := by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (n - i)))
    have hd : C * B ^ i / ((n - i).factorial : ℝ) ≤ C * B ^ i := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [mul_le_mul_of_nonneg_left hfac (by positivity : 0 ≤ C * B ^ i)]
    exact hd.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hi') hC)
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), C * B ^ n := Finset.sum_le_sum hterm
    _ = ((n + 1 : ℕ) : ℝ) * (C * B ^ n) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (n + 1) * (C * B ^ n) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (Nat.le_of_lt (n + 1).lt_two_pow_self)
    _ = _ := by rw [pow_succ, mul_pow]; ring

lemma descent_formal_coefficients_uniform (P : PsiTheory) :
    ∃ C B M₀ : ℝ, 0 < C ∧ 1 ≤ B ∧ 2 ≤ M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∀ L i : ℕ, i ≤ L → ∀ Y ∈ Icc (0 : ℝ) y₀,
      |PowerSeries.coeff i (formalGenus P Y 2)| ≤ C * B ^ i * scalarOrderWeight M L 1 ^ (2 * i) ∧
      |PowerSeries.coeff i (complexityShift (-1) (formalGenus P Y 2))| ≤ C * B ^ i * scalarOrderWeight M L 1 ^ (2 * i) ∧
      |PowerSeries.coeff i (formalCusp P Y 3)| ≤ C * B ^ i * scalarOrderWeight M L 1 ^ (2 * i) ∧
      |PowerSeries.coeff i ((formalCusp P Y 1)⁻¹)| ≤ C * B ^ i * scalarOrderWeight M L 1 ^ (2 * i) ∧
      |PowerSeries.coeff i (formalGenus P Y 1)| ≤ C * B ^ i * scalarOrderWeight M L 1 ^ (2 * i) := by
  obtain ⟨C₀, B₀, M₀, hC₀, hB₀, hM₀, hprofile, hscal⟩ := canonical_real_coefficient_bounds P
  obtain ⟨Ci, Bi, Mi, hCi, hBi, hMi, hinv⟩ := inverseCusp_coefficient_uniform_bound P
  let D : ℝ := max 1 (max B₀ Bi)
  let A : ℝ := C₀ * Real.exp 6 + Ci
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hA : 0 < A := by dsimp [A]; positivity
  have hB₀D : B₀ ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hBiD : Bi ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨2 * A, 2 * D, max (M₀ : ℝ) Mi, by positivity, by linarith, ?_, ?_⟩
  · exact (show (2 : ℝ) ≤ M₀ by exact_mod_cast hM₀).trans (le_max_left _ _)
  intro M hM L i hi Y hY
  have hM₀M : (M₀ : ℝ) ≤ M := (le_max_left _ _).trans hM
  have hMiM : Mi ≤ M := (le_max_right _ _).trans hM
  have hM2 : 2 ≤ M := hMi.trans hMiM
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hS (k : ℕ) : 0 ≤ scalarOrderWeight M k 1 := by unfold scalarOrderWeight; positivity
  have hcap (k : ℕ) (hk : k ≤ i) : scalarOrderWeight M k 1 ≤ scalarOrderWeight M L 1 := by
    unfold scalarOrderWeight
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (by exact_mod_cast hk.trans hi) hM0)
  have hscalar (p k : ℕ) (hp : 1 ≤ p) (hp3 : p ≤ 3) :
      |PowerSeries.coeff k (formalCusp P Y p)| + |PowerSeries.coeff k (formalGenus P Y p)| ≤
        A * D ^ k * scalarOrderWeight M k 1 ^ (2 * k) := by
    have hs := hscal k p hp Y hY
    simp only [formalCusp, formalGenus, PowerSeries.coeff_mk]
    apply hs.trans
    have hweight : scalarOrderWeight (M₀ : ℝ) k p ≤ (1 : ℝ) + M * (k + 1) + 2 := by
      have hpR : (p : ℝ) ≤ 3 := by exact_mod_cast hp3
      have hm := mul_le_mul_of_nonneg_right hM₀M (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      unfold scalarOrderWeight
      nlinarith
    have hpow := (pow_le_pow_left₀ (by unfold scalarOrderWeight; positivity) hweight (2 * k)).trans
      (by simpa only [Nat.cast_one] using ComplexCanonical.scalar_weight_succ_offset_pow M hM1 k 1 (by omega))
    have hb := pow_le_pow_left₀ hB₀.le hB₀D k
    have hC : C₀ * Real.exp 6 ≤ A := by dsimp [A]; linarith
    calc
      _ ≤ C₀ * B₀ ^ k * (Real.exp 6 * scalarOrderWeight M k 1 ^ (2 * k)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (C₀ * Real.exp 6) * D ^ k * scalarOrderWeight M k 1 ^ (2 * k) := by
        have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg hC₀.le (Real.exp_pos (6 : ℝ)).le) (pow_nonneg (hS k) (2 * k)))
        convert hh using 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (pow_nonneg hD.le k)) (pow_nonneg (hS k) _)
  have hg (k : ℕ) (hk : k ≤ i) :
      |PowerSeries.coeff k (formalGenus P Y 2)| ≤ A * D ^ k * scalarOrderWeight M L 1 ^ (2 * k) := by
    have hs := hscalar 2 k (by omega) (by omega)
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hs.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hS k) (hcap k hk) _) (by positivity)))
  have hc : |PowerSeries.coeff i (formalCusp P Y 3)| ≤ A * D ^ i * scalarOrderWeight M L 1 ^ (2 * i) := by
    have hs := hscalar 3 i (by omega) (by omega)
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hs.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hS i) (hcap i le_rfl) _) (by positivity)))
  have hi' : |PowerSeries.coeff i ((formalCusp P Y 1)⁻¹)| ≤ A * D ^ i * scalarOrderWeight M L 1 ^ (2 * i) := by
    have ht := hinv M hMiM 1 i (by omega) Y hY
    have hCiA : Ci ≤ A := by dsimp [A]; nlinarith [Real.exp_pos (6 : ℝ)]
    apply ht.trans
    apply mul_le_mul
    · exact mul_le_mul hCiA (pow_le_pow_left₀ hBi.le hBiD i) (by positivity) hA.le
    · exact pow_le_pow_left₀ (hS i) (hcap i le_rfl) _
    · exact pow_nonneg (hS i) _
    · positivity
  have hcommon : A * D ^ i ≤ (2 * A) * (2 * D) ^ i := by
    have hd := pow_le_pow_left₀ hD.le (show D ≤ 2 * D by linarith) i
    calc
      _ ≤ A * (2 * D) ^ i := mul_le_mul_of_nonneg_left hd hA.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hshift := complexityShift_coeff_exponential_majorant (-1) (scalarOrderWeight M L 1)
    (formalGenus P Y 2) (fun k => A * D ^ k) i (i + 1) (by omega)
    (by norm_num) (by
      have hiR : (i : ℝ) ≤ L := by exact_mod_cast hi
      unfold scalarOrderWeight
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) L])
    (fun k => by positivity) hg
  have hconv := exp_geometric_convolution_bound A D hA.le hD1 i
  have hshift' : |PowerSeries.coeff i (complexityShift (-1) (formalGenus P Y 2))| ≤
      2 * A * (2 * D) ^ i * scalarOrderWeight M L 1 ^ (2 * i) := by
    apply hshift.trans
    convert mul_le_mul_of_nonneg_left hconv (pow_nonneg (hS L) _) using 1 <;> ring
  refine ⟨?_, hshift', ?_, ?_, ?_⟩
  · exact (hg i le_rfl).trans (mul_le_mul_of_nonneg_right hcommon (pow_nonneg (hS L) _))
  · exact hc.trans (mul_le_mul_of_nonneg_right hcommon (pow_nonneg (hS L) _))
  · exact hi'.trans (mul_le_mul_of_nonneg_right hcommon (pow_nonneg (hS L) _))
  · have hs := hscalar 1 i (by omega) (by omega)
    apply (le_add_of_nonneg_left (abs_nonneg _)).trans (hs.trans _)
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hS i) (hcap i le_rfl) _) (by positivity)).trans
      (mul_le_mul_of_nonneg_right hcommon (pow_nonneg (hS L) _))
end WP.HigherOrder
