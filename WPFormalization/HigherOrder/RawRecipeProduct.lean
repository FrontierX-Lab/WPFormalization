import WPFormalization.HigherOrder.FixedSequenceProducts
import WPFormalization.Analysis.ExtractionDenominatorRegrading
/-! The original CG3 numerator/denominator recipe is recovered from a finite
prefix of its genuine Poisson-unit product. No coefficient family is replaced. -/
noncomputable section
namespace WP.HigherOrder
lemma rescaled_poisson_series_unit (ν:ℝ):
    PowerSeries.map Complex.ofRealHom (PowerSeries.rescale ν⁻¹ poissonStirlingSeries)*
      PowerSeries.map Complex.ofRealHom (PowerSeries.rescale ν⁻¹ (poissonStirlingSeries⁻¹))=1:=by
  rw[←map_mul,←map_mul,PowerSeries.mul_inv_cancel poissonStirlingSeries (by simp),map_one,map_one]
lemma raw_recipe_of_poisson_product_prefix (P:PsiTheory)(p:ℕ)(hp:1≤p)(x:ℝ)
    (hx:x∈Set.Ioo (0:ℝ) xCritical)(ap:PowerSeries ℂ)(N:ℕ)
    (he:∀j≤N,PowerSeries.coeff j (ap*
      PowerSeries.map Complex.ofRealHom (PowerSeries.rescale (WP.Psi x)⁻¹ poissonStirlingSeries))=
      ((PowerSeries.coeff (2*j) (extractionNumerator P p x):ℝ):ℂ)):
    ∀j≤N,PowerSeries.coeff j ap=
      ((PowerSeries.coeff (2*j) (extractionNumerator P p x*(extractionDenominator x)⁻¹):ℝ):ℂ):=by
  let num:PowerSeries ℂ:=PowerSeries.mk (fun j=>((PowerSeries.coeff (2*j) (extractionNumerator P p x):ℝ):ℂ))
  let den:PowerSeries ℂ:=PowerSeries.map Complex.ofRealHom (PowerSeries.rescale (WP.Psi x)⁻¹ poissonStirlingSeries)
  let invden:PowerSeries ℂ:=PowerSeries.map Complex.ofRealHom (PowerSeries.rescale (WP.Psi x)⁻¹ (poissonStirlingSeries⁻¹))
  have hunit:den*invden=1:=rescaled_poisson_series_unit (WP.Psi x)
  have hprefix:=coeff_from_product_prefix_right_inverse ap den invden num hunit N
    (by intro j hj;simpa only[num,den,PowerSeries.coeff_mk] using he j hj)
  intro j hj
  rw[hprefix j hj,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw[WP.Analysis.raw_extraction_complex_morse_convolution P p hp x hx j
    (fun i=>((PowerSeries.coeff (2*i) (extractionNumerator P p x):ℝ):ℂ)) (fun i hi=>rfl)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only[num,invden,PowerSeries.coeff_mk,PowerSeries.coeff_map,PowerSeries.coeff_rescale]
  change ((PowerSeries.coeff (2*i) (extractionNumerator P p x):ℝ):ℂ)*
      (((WP.Psi x)⁻¹^(j-i)*PowerSeries.coeff (j-i) poissonStirlingSeries⁻¹:ℝ):ℂ)=_
  push_cast
  ring
end WP.HigherOrder
