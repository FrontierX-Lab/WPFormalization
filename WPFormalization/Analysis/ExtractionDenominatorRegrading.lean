import WPFormalization.Volumes.RawExtractionIntegral
import Mathlib.RingTheory.PowerSeries.Expand
/-! Exact even regrading of the original CG3 numerator and inverse Poisson denominator. The original extraction definitions are unchanged. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma powerSeries_rescale_inv_unit (t:ℝ) (F:PowerSeries ℝ) (hF:PowerSeries.constantCoeff F≠0) :
    PowerSeries.rescale t F⁻¹=(PowerSeries.rescale t F)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by
    simpa only[←PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_rescale,pow_zero,one_mul] using hF)).mpr
  rw[←map_mul,PowerSeries.inv_mul_cancel F hF,map_one]

lemma powerSeries_expand_inv_unit (F:PowerSeries ℝ) (hF:PowerSeries.constantCoeff F≠0) :
    PowerSeries.expand 2 (by norm_num) F⁻¹=(PowerSeries.expand 2 (by norm_num) F)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simpa only[PowerSeries.constantCoeff_expand] using hF)).mpr
  rw[←map_mul,PowerSeries.inv_mul_cancel F hF,map_one]

lemma extractionDenominator_eq_even_rescale (x:ℝ) :
    HigherOrder.extractionDenominator x=PowerSeries.expand 2 (by norm_num)
      (PowerSeries.rescale ((WP.Psi x)⁻¹) HigherOrder.poissonStirlingSeries) := by
  ext n
  simp only[HigherOrder.extractionDenominator,PowerSeries.coeff_mk,PowerSeries.coeff_expand,PowerSeries.coeff_rescale]
  by_cases hn:Even n
  · have hd:2∣n:=even_iff_two_dvd.mp hn
    simp only[ite_eq_left hn,ite_eq_left hd]
    ring
  · have hd:¬2∣n:=by simpa only[←even_iff_two_dvd] using hn
    simp only[ite_eq_right hn,ite_eq_right hd]

lemma extractionDenominator_inv_eq_even_rescale (x:ℝ) :
    (HigherOrder.extractionDenominator x)⁻¹=PowerSeries.expand 2 (by norm_num)
      (PowerSeries.rescale ((WP.Psi x)⁻¹) (HigherOrder.poissonStirlingSeries⁻¹)) := by
  have hP:PowerSeries.constantCoeff HigherOrder.poissonStirlingSeries≠0:=by simp
  have hR:PowerSeries.constantCoeff (PowerSeries.rescale ((WP.Psi x)⁻¹) HigherOrder.poissonStirlingSeries)≠0:=by
    simpa only[←PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_rescale,pow_zero,one_mul] using hP
  rw[extractionDenominator_eq_even_rescale,←powerSeries_expand_inv_unit _ hR,←powerSeries_rescale_inv_unit _ _ hP]

def extractionEvenNumerator (P:PsiTheory) (p:ℕ) (x:ℝ):PowerSeries ℝ:=
  PowerSeries.mk (fun j=>PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x))

lemma extractionNumerator_eq_even_expansion (P:PsiTheory) (p:ℕ) (hp:1≤p) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) :
    HigherOrder.extractionNumerator P p x=PowerSeries.expand 2 (by norm_num) (extractionEvenNumerator P p x) := by
  ext n
  by_cases hn:Even n
  · obtain ⟨k,hk⟩:=hn
    have he:n=2*k:=by omega
    rw[he,PowerSeries.coeff_expand_mul]
    simp only[extractionEvenNumerator,PowerSeries.coeff_mk]
  · have hn2:¬2∣n:=by simpa only[←even_iff_two_dvd] using hn
    rw[PowerSeries.coeff_expand_of_not_dvd _ _ _ hn2,
      extractionNumerator_odd_coefficient_zero P p hp x hx n (Nat.not_even_iff_odd.mp hn)]

lemma raw_extraction_even_product_coefficient (P:PsiTheory) (p:ℕ) (hp:1≤p) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) (j:ℕ) :
    PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x*(HigherOrder.extractionDenominator x)⁻¹)=
      PowerSeries.coeff j (extractionEvenNumerator P p x*
        PowerSeries.rescale ((WP.Psi x)⁻¹) (HigherOrder.poissonStirlingSeries⁻¹)) := by
  rw[extractionNumerator_eq_even_expansion P p hp x hx,extractionDenominator_inv_eq_even_rescale,
    ←map_mul,PowerSeries.coeff_expand_mul]

lemma raw_extraction_complex_morse_convolution (P:PsiTheory) (p:ℕ) (hp:1≤p) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) (j:ℕ) (g:ℕ→ℂ)
    (hg:∀i≤j,((PowerSeries.coeff (2*i) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)=g i) :
    ((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x*(HigherOrder.extractionDenominator x)⁻¹):ℝ):ℂ)=
      ∑i∈Finset.range (j+1),g i*((PowerSeries.coeff (j-i) (HigherOrder.poissonStirlingSeries⁻¹):ℝ):ℂ)/(WP.Psi x:ℂ)^(j-i) := by
  rw[raw_extraction_even_product_coefficient P p hp x hx j,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only[extractionEvenNumerator,PowerSeries.coeff_mk,PowerSeries.coeff_rescale]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw[hg i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  simp only[inv_pow,div_eq_mul_inv]
  ring

lemma rawExtractedCoefficient_complex_morse_convolution (P:PsiTheory) (p:ℕ) (hp:1≤p) (Y:ℝ)
    (hx:XR Y∈Ioo (0:ℝ) xCritical) (j:ℕ) (g:ℕ→ℂ)
    (hg:∀i≤j,((PowerSeries.coeff (2*i) (HigherOrder.extractionNumerator P p (XR Y)):ℝ):ℂ)=g i) :
    (HigherOrder.rawExtractedCoefficient P p j Y:ℂ)=
      ∑i∈Finset.range (j+1),g i*((PowerSeries.coeff (j-i) (HigherOrder.poissonStirlingSeries⁻¹):ℝ):ℂ)/(WP.Psi (XR Y):ℂ)^(j-i) := by
  exact raw_extraction_complex_morse_convolution P p hp (XR Y) hx j g hg
end WP.Analysis
