import WPFormalization.HigherOrder.SecondSeparatingCoefficients
import WPFormalization.HigherOrder.SecondTransportFinite

/-! The actual triangular profile, cusp and transport coefficients through second order agree with the explicit Appendix C coefficients. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

lemma adjacentCoefficient_two_closed (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀)
    (i : ℕ) (d : List ℕ) (hi : i<d.length) :
    adjacentCoefficient P Y (hierarchyJet P Y 1) 2 i d= -secondIncrement Y i d := by
  unfold adjacentCoefficient
  simp only [map_add]
  rw [mergerSeries_two P Y hY,nonseparatingSeries_two P Y hY,separatingSeries_two P Y hY]
  have he : (d.eraseIdx i).length=d.length-1 := List.length_eraseIdx_of_lt hi
  have h₁ : d.length-1+1=d.length := by omega
  have h₂ : d.length-1+2=d.length+1 := by omega
  simp only [he,h₁,h₂]
  unfold secondIncrement
  simp only [he,h₁,h₂]

lemma profileCoefficient_two (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (d : List ℕ) :
    profileCoefficient P Y d 2=secondProfile Y d := by
  change PowerSeries.coeff 2 (setCoeff ((hierarchyJet P Y 1).profile d) 2
    (profileAtOrder P Y (hierarchyJet P Y 1) 2 d))=_
  rw [setCoeff_same]
  unfold profileAtOrder secondProfile
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact adjacentCoefficient_two_closed P Y hY i (beforeCoordinate d i t)
    (by simpa [beforeCoordinate_length] using Finset.mem_range.mp hi)

lemma cuspCoefficient_two (P : PsiTheory) (p : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    cuspCoefficient P Y p 2=transportBeta p Y+secondDilatonMoment p Y/A Y := by
  have hf : cuspCoefficient P Y p 2=PowerSeries.coeff 2 (cuspSeries Y (formalProfile P Y) p) := by
    rw [←formalCusp_recursion P Y hY p]
    simp only [formalCusp,PowerSeries.coeff_mk]
  rw [hf]
  simp only [cuspSeries,PowerSeries.coeff_C_mul,coefficientSum_coeff,complexityShift_two,
    formalProfile,PowerSeries.coeff_mk,profileCoefficient_one P Y hY,profileCoefficient_two P Y hY,
    bCoeff_eq_canonicalDilatonCoefficient]
  have he:=secondDilatonMoment_hasSum p Y hY
  have hd:=canonicalDilaton_degreeCorrection_hasSum_beta p Y hY
  have hs : HasSum (fun d:ℕ=>canonicalDilatonCoefficient Y (d+1)*
      (secondProfile Y ((d+1)::List.replicate p 0)+degreeCorrection ((d+1)::List.replicate p 0) Y))
      (secondDilatonMoment p Y+A Y*transportBeta p Y) := by
    apply (hasSum_nat_add_iff (f:=fun d:ℕ=>canonicalDilatonCoefficient Y d*
      (secondProfile Y (d::List.replicate p 0)+degreeCorrection (d::List.replicate p 0) Y)) 1).mpr
    have hh:=he.add hd
    have hz : canonicalDilatonCoefficient Y 0=0 := by simp [canonicalDilatonCoefficient]
    simp only [Finset.sum_range_one,hz,zero_mul,add_zero]
    convert! hh using 1
    funext d
    ring
  have hsum : (∑'d:ℕ,canonicalDilatonCoefficient Y (d+1)*
      (secondProfile Y ((d+1)::List.replicate p 0)+(-1)* -degreeCorrection ((d+1)::List.replicate p 0) Y))=
      secondDilatonMoment p Y+A Y*transportBeta p Y := by
    convert! hs.tsum_eq using 1
    congr 1
    funext d
    ring
  rw [hsum]
  have hA:=A_ne_zero_closed Y hY
  field_simp <;>ring

lemma transportCoefficient_one (P : PsiTheory) (p : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    transportCoefficient P p 1 Y=transportGamma p Y := by
  rw [transportCoefficient_one_algebra,cuspCoefficient_one P p Y hY,cuspCoefficient_two P p Y hY,
    transportGamma_eq_secondDilatonMoment p Y hY]
  ring

lemma markedCoefficient_one_eq_firstMarkedCorrection (P : PsiTheory) (p : ℕ)
    (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) : markedCoefficient P p 1 Y=firstMarkedCorrection p Y := by
  rw [markedCoefficient_one,firstMarkedCorrection]
  congr 1
  apply intervalIntegral.integral_congr
  intro v hv
  have hv' : v∈Set.Icc (0:ℝ) y₀ := by
    rw [Set.uIcc_of_le hY.2] at hv
    exact ⟨hY.1.trans hv.1,hv.2⟩
  change transportCoefficient P p 1 v/(A v*r v)=transportGamma p v/(A v*r v)
  rw [transportCoefficient_one P p v hv']

end WP.HigherOrder
