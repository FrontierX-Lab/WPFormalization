import WPFormalization.Volumes.BoundaryPolynomial
import WPFormalization.Volumes.PositiveConvolutionAnalytic

noncomputable section
namespace WP.BoundaryConvolution
open Set Filter PositiveConvolution
open scoped Topology

lemma boundary_single_weight_normalization (L : ℝ) (b : ℕ) :
    (L^2/(4*Real.pi^2))^b/((b.factorial:ℝ)*(oddFactorial b:ℝ)) =
      (L^2/(2*Real.pi^2))^b/((2*b+1).factorial:ℝ) := by
  have ho : (b.factorial:ℝ)*(oddFactorial b:ℝ)*(2:ℝ)^b =
      ((2*b+1).factorial:ℝ) := by
    exact_mod_cast Analysis.oddFactorial_factorial b
  have hb : L^2/(2*Real.pi^2) = 2*(L^2/(4*Real.pi^2)) := by
    field_simp
    <;> ring
  rw [hb,mul_pow,←ho]
  have hn : (2:ℝ)^b ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

lemma boundaryDegreeWeight_scale (p : ℕ) (L : Fin p → ℝ) (b : Fin p → ℕ) :
    boundaryDegreeWeight p L b =
      (∏ i, L i^(2*b i)/((2*b i+1).factorial:ℝ))/(4:ℝ)^(∑ i,b i) := by
  unfold boundaryDegreeWeight
  simp only [div_mul_eq_div_div]
  simp only [Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]
  ring

lemma boundary_polynomial_term_normalization (P : PsiTheory) (g p : ℕ)
    (L : Fin p → ℝ) (b : Fin p → ℕ) (hb : b ∈ degreeTuples g p) :
    mixedBracket P g (List.ofFn b)*boundaryDegreeWeight p L b /
      (2*Real.pi^2)^(dimension g p) =
      shifted P g (List.ofFn b) 0 /
        (∏ i, (oddFactorial (b i):ℝ)) *
          ∏ i, ((L i)^2/(4*Real.pi^2))^(b i)/(b i).factorial := by
  have hd := (mem_degreeTuples_iff g p b).mp hb
  have hD : dimension g p = (∑ i,b i)+deficit g (List.ofFn b) := by
    simp only [deficit,List.sum_ofFn,List.length_ofFn]
    omega
  have hp : (2*Real.pi^2:ℝ) ≠ 0 := by positivity
  have h4 : (4:ℝ)^(∑ i,b i) ≠ 0 := by positivity
  have hpow : (2*Real.pi^2:ℝ)^(∑ i,b i) ≠ 0 := pow_ne_zero _ hp
  have hpowd : (2*Real.pi^2:ℝ)^(deficit g (List.ofFn b)) ≠ 0 := pow_ne_zero _ hp
  rw [mixedBracket,boundaryDegreeWeight_scale,hD,pow_add]
  simp only [List.sum_ofFn]
  have he : ((4:ℝ)^(∑ i,b i)*(2*Real.pi^2)^(deficit g (List.ofFn b))*
      shifted P g (List.ofFn b) 0 *
      ((∏ i,L i^(2*b i)/(2*b i+1).factorial)/4^(∑ i,b i))) /
      ((2*Real.pi^2)^(∑ i,b i)*(2*Real.pi^2)^(deficit g (List.ofFn b))) =
      shifted P g (List.ofFn b) 0 *
        ((∏ i,L i^(2*b i)/(2*b i+1).factorial)/(2*Real.pi^2)^(∑ i,b i)) := by
    field_simp
  rw [he]
  rw [←Finset.prod_pow_eq_pow_sum,←Finset.prod_div_distrib]
  have hi (i : Fin p) :
      (L i^(2*b i)/(2*b i+1).factorial)/(2*Real.pi^2)^(b i) =
        ((L i)^2/(4*Real.pi^2))^(b i) /
          (((b i).factorial:ℝ)*(oddFactorial (b i):ℝ)) := by
    rw [boundary_single_weight_normalization]
    rw [div_pow,pow_mul]
    ring
  simp only [hi]
  simp only [Finset.prod_div_distrib,Finset.prod_mul_distrib]
  ring

end WP.BoundaryConvolution
