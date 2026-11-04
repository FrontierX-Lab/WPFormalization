import WPFormalization.Volumes.FixedCuspProof
import WPFormalization.Volumes.LeadingNormalization

noncomputable section
namespace WP
open Set
lemma marked_realCoeff_volume (P : PsiTheory) (g p k : ℕ) :
    realCoeff (iteratedDeriv p (Phi P g)) k =
      volumeModel P g (k+p) / ((2*Real.pi^2)^(dimension g (k+p))*(k.factorial:ℝ)) := by
  rw [realCoeff,coeff,Analysis.iteratedDeriv_iteratedDeriv_eq,
    PositiveConvolution.Phi_iteratedDeriv_zero]
  have he : ((shifted P g (List.replicate (k+p) 0) 0:ℂ)/(k.factorial:ℂ)).re =
      shifted P g (List.replicate (k+p) 0) 0/(k.factorial:ℝ) := by norm_cast
  rw [he]
  simp only [volumeModel,mixedBracket,List.sum_replicate,nsmul_zero,pow_zero,one_mul,
    deficit,List.length_replicate,Nat.sub_zero]
  field_simp [Real.pi_ne_zero]

lemma volume_ratio_error_quotient (a b A B t : ℝ) (ht : 0 < t)
    (ha : |a-1| ≤ A/t) (hb : |b-1| ≤ B/t) (hB : B/t ≤ 1/2) :
    |a/b-1| ≤ 2*(A+B)/t := by
  have hb0 : (1:ℝ)/2 ≤ b := by have := (abs_le.mp hb).1; linarith
  have hbn : b ≠ 0 := by linarith
  have he : a/b-1 = ((a-1)-(b-1))/b := by field_simp <;> ring
  rw [he,abs_div,abs_of_pos (by linarith : 0 < b)]
  apply (div_le_div_iff₀ (by linarith : 0 < b) ht).mpr
  have hab : |(a-1)-(b-1)| ≤ (A+B)/t :=
    (abs_sub (a-1) (b-1)).trans (by rw [add_div]; exact add_le_add ha hb)
  have hAB : 0 ≤ A+B := by
    have := (abs_nonneg ((a-1)-(b-1))).trans hab
    simpa only [zero_mul] using (le_div_iff₀ ht).mp this
  have hmul := (le_div_iff₀ ht).mp hab
  nlinarith only [hmul, mul_nonneg hAB (show 0 ≤ b-1/2 by linarith)]

lemma volume_ratio_error_product (a b A B t : ℝ) (ht : 1 ≤ t)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : |a-1| ≤ A/t) (hb : |b-1| ≤ B/t) :
    |a*b-1| ≤ (A+B+A*B)/t := by
  have ht0 : 0 < t := by linarith
  have he : a*b-1=(a-1)+(b-1)+(a-1)*(b-1) := by ring
  rw [he]
  have hprod : |a-1| * |b-1| ≤ (A/t)*(B/t) :=
    mul_le_mul ha hb (abs_nonneg _) (by positivity)
  have hsum := abs_add_le ((a-1)+(b-1)) ((a-1)*(b-1))
  have hs := abs_add_le (a-1) (b-1)
  rw [abs_mul] at hsum
  have hAB : (A/t)*(B/t) ≤ (A*B)/t := by
    have hAt : 0 ≤ A/t := by positivity
    have hBt : B/t ≤ B := (div_le_iff₀ ht0).mpr (by nlinarith)
    calc
      _ ≤ (A/t)*B := mul_le_mul_of_nonneg_left hBt hAt
      _ = _ := by ring
  rw [add_div,add_div]
  linarith

lemma fixedCuspLeadingScale_pos (g n : ℕ) (hg : 1 ≤ g) :
    0 < fixedCuspLeadingScale g n := by
  have hgR : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  unfold fixedCuspLeadingScale
  positivity

lemma fixedCuspLeadingScale_succ_ratio (g n : ℕ) (hg : 2 ≤ g) :
    fixedCuspLeadingScale g (n+1)/(2*g*fixedCuspLeadingScale g n) /
      (4*Real.pi^2) = 1+((n:ℝ)-2)/(2*g) := by
  have hgR : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  have he : 2*g+(n+1)-3=(2*g+n-3)+1 := by omega
  have hec : ((2*g+n-3+1:ℕ):ℝ) = 2*(g:ℝ)+n-2 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only [fixedCuspLeadingScale,he,Nat.factorial_succ,pow_succ,Nat.cast_mul]
  rw [hec]
  have hfac : ((2*g+n-3).factorial:ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt (Real.pi*g) ≠ 0 := by positivity
  have hpow : (4*Real.pi^2)^(2*g+n-3) ≠ (0:ℝ) := by positivity
  field_simp [hfac,hsqrt,hpow,Real.pi_ne_zero,hgR.ne']
  <;> ring

lemma fixedCuspLeadingScale_genus_ratio (g : ℕ) (hg : 2 ≤ g) :
    fixedCuspLeadingScale g 0/fixedCuspLeadingScale (g-1) 2 =
      Real.sqrt (((g:ℝ)-1)/g) := by
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg
  have he : 2*(g-1)+2-3 = 2*g-3 := by omega
  have hgc : ((g-1:ℕ):ℝ)=(g:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hs : Real.sqrt (Real.pi*(g:ℝ)) ≠ 0 := by positivity
  have hgm : 0 < (g:ℝ)-1 := by linarith
  have hs' : Real.sqrt (Real.pi*((g:ℝ)-1)) ≠ 0 := by positivity
  have hfac : ((2*g-3).factorial:ℝ) ≠ 0 := by positivity
  have hpow : (4*Real.pi^2)^(2*g-3) ≠ (0:ℝ) := by positivity
  simp only [fixedCuspLeadingScale,he,hgc,Nat.add_zero]
  calc
    _ = Real.sqrt (Real.pi*((g:ℝ)-1))/Real.sqrt (Real.pi*g) := by
      field_simp [hs,hs',hfac,hpow]
    _ = _ := by
      rw [← Real.sqrt_div (by positivity : 0 ≤ Real.pi*((g:ℝ)-1))]
      congr 1
      field_simp

lemma fixedCuspLeadingScale_genus_ratio_error (g : ℕ) (hg : 2 ≤ g) :
    |fixedCuspLeadingScale g 0/fixedCuspLeadingScale (g-1) 2-1| ≤ 1/(g:ℝ) := by
  rw [fixedCuspLeadingScale_genus_ratio g hg]
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0:ℝ) < g := by linarith
  have hgm : 0 < (g:ℝ)-1 := by linarith
  have ht : 0 ≤ ((g:ℝ)-1)/g := by positivity
  have ht1 : ((g:ℝ)-1)/g ≤ 1 := (div_le_iff₀ hg0).mpr (by linarith)
  have hs := Real.sqrt_nonneg (((g:ℝ)-1)/g)
  have hs1 : Real.sqrt (((g:ℝ)-1)/g) ≤ 1 := (Real.sqrt_le_one).mpr ht1
  have he := Real.sq_sqrt ht
  rw [abs_of_nonpos (by linarith)]
  have hsq : ((g:ℝ)-1)/g ≤ Real.sqrt (((g:ℝ)-1)/g) := by nlinarith
  have hd : ((g:ℝ)-1)/g = 1-1/g := by field_simp <;> ring
  have hlinear : 1-1/g ≤ Real.sqrt (((g:ℝ)-1)/g) := by
    calc
      _ = ((g:ℝ)-1)/g := hd.symm
      _ ≤ _ := hsq
  linarith

lemma profileB_zero_volume_ratios : profileB 0=1 := by
  rw [profileB,densityY_zero_parameter,Delta,T_zero_value,sub_zero]
  field_simp [Real.pi_ne_zero]

lemma profileC_zero_volume_ratios : profileC 0=4*Real.pi^2 := by simp [profileC]

lemma volume_ratios_zero_cusp_genus (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G,
      |(volumeModel P g 0/volumeModel P (g-1) 2)/profileB 0-1| ≤ C/g := by
  obtain ⟨A,hA,G₀,ha⟩ := zograf_constant_proof P 0
  obtain ⟨B,hB,G₂,hb⟩ := zograf_constant_proof P 2
  obtain ⟨K,hK⟩ := exists_nat_gt (4*B)
  let D : ℝ := 2*(A+2*B)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D+1+D,by positivity,max (max G₀ (G₂+1)) (K+2),?_⟩
  intro g hg
  have hg2 : 2 ≤ g := by omega
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg2
  have hg0 : (0:ℝ) < g := by linarith
  have hgm : 0 < (g:ℝ)-1 := by linarith
  have hcast : ((g-1:ℕ):ℝ)=(g:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have ha' : |volumeModel P g 0/fixedCuspLeadingScale g 0-1| ≤ A/g := ha g (by omega)
  have hb' : |volumeModel P (g-1) 2/fixedCuspLeadingScale (g-1) 2-1| ≤ 2*B/g := by
    have hh := hb (g-1) (by omega)
    change |volumeModel P (g-1) 2/fixedCuspLeadingScale (g-1) 2-1| ≤ B/((g-1:ℕ):ℝ) at hh
    rw [hcast] at hh
    apply hh.trans
    apply (div_le_div_iff₀ hgm hg0).mpr
    nlinarith
  have hsmall : 2*B/(g:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hg0).mpr
    have hKg : (K:ℝ) ≤ g := by exact_mod_cast (show K ≤ g by omega)
    linarith
  have hq := volume_ratio_error_quotient _ _ A (2*B) g hg0 ha' hb' hsmall
  change |_ - 1| ≤ D/g at hq
  have hden : volumeModel P (g-1) 2 ≠ 0 := by
    intro hz
    rw [hz,zero_div,zero_sub,abs_neg,abs_one] at hb'
    linarith
  have hs := fixedCuspLeadingScale_genus_ratio_error g hg2
  have hprod := volume_ratio_error_product _ _ D 1 g (by linarith) hD.le zero_le_one hq hs
  rw [profileB_zero_volume_ratios,div_one]
  convert hprod using 1
  · congr 2
    have hs0 := (fixedCuspLeadingScale_pos g 0 (by omega)).ne'
    have hs2 := (fixedCuspLeadingScale_pos (g-1) 2 (by omega)).ne'
    field_simp [hs0,hs2,hden]
  · ring

lemma volume_ratios_zero_cusp_add (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G,
      |(volumeModel P g 1/(2*g*volumeModel P g 0))/profileC 0-1| ≤ C/g := by
  obtain ⟨A,hA,G₁,ha⟩ := zograf_constant_proof P 1
  obtain ⟨B,hB,G₀,hb⟩ := zograf_constant_proof P 0
  obtain ⟨K,hK⟩ := exists_nat_gt (2*B)
  let D : ℝ := 2*(A+B)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D+1+D,by positivity,max (max G₁ G₀) (K+2),?_⟩
  intro g hg
  have hg2 : 2 ≤ g := by omega
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg2
  have hg0 : (0:ℝ) < g := by linarith
  have ha' : |volumeModel P g 1/fixedCuspLeadingScale g 1-1| ≤ A/g := ha g (by omega)
  have hb' : |volumeModel P g 0/fixedCuspLeadingScale g 0-1| ≤ B/g := hb g (by omega)
  have hsmall : B/(g:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hg0).mpr
    have hKg : (K:ℝ) ≤ g := by exact_mod_cast (show K ≤ g by omega)
    linarith
  have hq := volume_ratio_error_quotient _ _ A B g hg0 ha' hb' hsmall
  change |_ - 1| ≤ D/g at hq
  have hden : volumeModel P g 0 ≠ 0 := by
    intro hz
    rw [hz,zero_div,zero_sub,abs_neg,abs_one] at hb'
    linarith
  have hs : |fixedCuspLeadingScale g 1/(2*g*fixedCuspLeadingScale g 0)/
      (4*Real.pi^2)-1| ≤ 1/(g:ℝ) := by
    rw [fixedCuspLeadingScale_succ_ratio g 0 hg2]
    norm_num
    rw [abs_div,abs_mul,abs_of_pos hg0]
    norm_num [div_eq_mul_inv]
    ring_nf
    rfl
  have hprod := volume_ratio_error_product _ _ D 1 g (by linarith) hD.le zero_le_one hq hs
  rw [profileC_zero_volume_ratios]
  convert hprod using 1
  · congr 2
    have hs0 := (fixedCuspLeadingScale_pos g 0 (by omega)).ne'
    have hs1 := (fixedCuspLeadingScale_pos g 1 (by omega)).ne'
    field_simp [hs0,hs1,hden,Real.pi_ne_zero,hg0.ne']
    <;> ring
  · ring

lemma volume_ratios_zero_cusp (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G,
      |(volumeModel P g 0/volumeModel P (g-1) 2)/profileB 0-1| ≤ C/g ∧
      |(volumeModel P g 1/(2*g*volumeModel P g 0))/profileC 0-1| ≤ C/g := by
  obtain ⟨A,hA,G₀,ha⟩ := volume_ratios_zero_cusp_genus P
  obtain ⟨B,hB,G₁,hb⟩ := volume_ratios_zero_cusp_add P
  refine ⟨A+B,by positivity,max G₀ G₁,?_⟩
  intro g hg
  have hg0 : 0 ≤ (g:ℝ) := by positivity
  constructor
  · exact (ha g (by omega)).trans (div_le_div_of_nonneg_right (by linarith) hg0)
  · exact (hb g (by omega)).trans (div_le_div_of_nonneg_right (by linarith) hg0)
end WP
