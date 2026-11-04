import WPFormalization.HigherOrder.HierarchyIdentities
import WPFormalization.HigherOrder.LowOrderAlgebra
import WPFormalization.Marked.DilatonCorrection

/-! The actual first cusp and genus coefficients at every marking count, including both descent steps. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

lemma bCoeff_eq_canonicalDilatonCoefficient (Y : ℝ) (d : ℕ) :
    bCoeff Y d=canonicalDilatonCoefficient Y d := by
  by_cases hd : d=0
  · simp [bCoeff,canonicalDilatonCoefficient,hd]
  · simp [bCoeff,canonicalDilatonCoefficient,hd,show 1≤d by omega]

lemma canonicalDilaton_degreeCorrection_hasSum_beta (p : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    HasSum (fun d : ℕ=>canonicalDilatonCoefficient Y d*degreeCorrection (d::List.replicate p 0) Y)
      (A Y*transportBeta p Y) := by
  exact canonicalDilaton_degreeCorrection_hasSum p Y hY

lemma cuspCoefficient_one (P : PsiTheory) (p : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    cuspCoefficient P Y p 1= -transportBeta p Y := by
  have hf : cuspCoefficient P Y p 1=PowerSeries.coeff 1 (cuspSeries Y (formalProfile P Y) p) := by
    rw [←formalCusp_recursion P Y hY p]
    simp only [formalCusp,PowerSeries.coeff_mk]
  rw [hf]
  simp only [cuspSeries,PowerSeries.coeff_C_mul,coefficientSum_coeff,
    complexityShift_one,formalProfile,PowerSeries.coeff_C_mul,PowerSeries.coeff_mk,
    profileCoefficient_one P Y hY,bCoeff_eq_canonicalDilatonCoefficient]
  have hs:=canonicalDilaton_degreeCorrection_hasSum_beta p Y hY
  have hshift : HasSum (fun d : ℕ=>canonicalDilatonCoefficient Y (d+1)*
      degreeCorrection ((d+1)::List.replicate p 0) Y) (A Y*transportBeta p Y) := by
    apply (hasSum_nat_add_iff (f:=fun d:ℕ=>canonicalDilatonCoefficient Y d*degreeCorrection (d::List.replicate p 0) Y) 1).mpr
    simpa [Finset.sum_range_one,canonicalDilatonCoefficient] using hs
  have he : (∑'d:ℕ,canonicalDilatonCoefficient Y (d+1)* -degreeCorrection ((d+1)::List.replicate p 0) Y)=
      -(A Y*transportBeta p Y) := by
    convert! hshift.neg.tsum_eq using 1
    congr 1
    ext d
    ring
  rw [he]
  have hA:=A_ne_zero_closed Y hY
  field_simp

lemma genusCoefficient_one_low (P : PsiTheory) (p : ℕ) (hp : p≤1)
    (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀)
    (hnext : genusCoefficient P Y (p+1) 1= -alpha (p+1) Y) :
    genusCoefficient P Y p 1= -alpha p Y := by
  have hd:=congrArg (fun f:Series=>PowerSeries.coeff 1 f) (formalGenus_descent P Y p hp)
  simp only [descendGenus,PowerSeries.coeff_one_mul,map_mul,
    complexityShift_constant,formalGenus_constant,formalCusp_constant,
    constantCoeff_inv,inv_one,complexityShift_one,coeff_one_inv_unit _ (formalCusp_constant P Y p),
    one_mul,mul_one] at hd
  simp only [formalCusp,formalGenus,PowerSeries.coeff_mk] at hd
  rw [hnext,cuspCoefficient_one P (p+2) Y hY,cuspCoefficient_one P p Y hY] at hd
  rw [hd]
  unfold alpha transportBeta
  push_cast
  ring

lemma genusCoefficient_one (P : PsiTheory) (p : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    genusCoefficient P Y p 1= -alpha p Y := by
  have h₂:=genusCoefficient_one_high P Y hY 2 (by omega)
  have h₁:=genusCoefficient_one_low P 1 (by omega) Y hY h₂
  have h₀:=genusCoefficient_one_low P 0 (by omega) Y hY h₁
  rcases p with _|_|p
  · exact h₀
  · exact h₁
  · exact genusCoefficient_one_high P Y hY (p+2) (by omega)

end WP.HigherOrder
