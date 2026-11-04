import WPFormalization.Marked.SignedDilatonMoments
import WPFormalization.Analysis.KernelWeightMoments
/-! Exact summation of the first degree correction against the canonical dilaton coefficients.
The second H jet is eliminated using the normalized kernel identity and the true weight mass. -/
noncomputable section
namespace WP
lemma degreeCorrection_single_positive (d p : ℕ) (hd : 0<d) (Y : ℝ) :
    degreeCorrection (d::List.replicate p 0) Y = A Y*
      (Theta Y*((d:ℝ)^2+((p:ℝ)-3)*d)+2*moment₁ Y*d+2-p) := by
  have hf : (d::List.replicate p 0).filter (fun k => 0<k)=[d] := by simp [hd]
  simp only [degreeCorrection,hf,List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,
    List.length_cons,List.length_nil,List.length_replicate,Nat.cast_zero,Nat.cast_add,Nat.cast_one]
  ring
lemma canonicalDilaton_degreeCorrection_polynomial (d p : ℕ) (Y : ℝ) :
    canonicalDilatonCoefficient Y d*degreeCorrection (d::List.replicate p 0) Y =
      A Y*(Theta Y*((d:ℝ)^2*canonicalDilatonCoefficient Y d+
          ((p:ℝ)-3)*((d:ℝ)*canonicalDilatonCoefficient Y d))+
        2*moment₁ Y*((d:ℝ)*canonicalDilatonCoefficient Y d)+
        (2-(p:ℝ))*canonicalDilatonCoefficient Y d) := by
  by_cases hd : d=0
  · subst d
    simp [canonicalDilatonCoefficient]
  · rw [degreeCorrection_single_positive d p (by omega) Y]
    ring
lemma canonicalDilaton_degreeCorrection_hasSum_raw (p : ℕ) (Y : ℝ) (hY : Y ∈ Set.Icc (0:ℝ) y₀) :
    HasSum (fun d : ℕ => canonicalDilatonCoefficient Y d*degreeCorrection (d::List.replicate p 0) Y)
      (A Y*(Theta Y*((deriv (deriv (barH Y)) 1).re/3-7*A Y/2+
          ((p:ℝ)-3)*(-(A Y)/2))+
        2*moment₁ Y*(-(A Y)/2)+(2-(p:ℝ))*A Y)) := by
  have h₀ := canonicalDilatonCoefficient_hasSum Y
  have h₁ := canonicalDilatonCoefficient_first_hasSum Y hY
  have h₂ := canonicalDilatonCoefficient_second_hasSum Y hY
  have hs := (((h₂.add (h₁.mul_left ((p:ℝ)-3))).mul_left (Theta Y)).add
    (h₁.mul_left (2*moment₁ Y))).add (h₀.mul_left (2-(p:ℝ)))
  have ht := hs.mul_left (A Y)
  convert! ht using 1
  ext d
  exact canonicalDilaton_degreeCorrection_polynomial d p Y

lemma barH_second_theta_identity (Y : ℝ) (hY : Y ∈ Set.Icc (0:ℝ) y₀) :
    Theta Y*((deriv (deriv (barH Y)) 1).re/3) =
      15/4*A Y*Theta Y-1/2 := by
  have hH := barH_differentiable Y
  have hp := ((hH 1).hasDerivAt).add
    ((((hasDerivAt_id (1:ℂ)).const_mul (2/3:ℂ)).mul ((hH.deriv 1).hasDerivAt)))
  have he : (fun z : ℂ => barH Y z+(2/3:ℂ)*z*deriv (barH Y) z)=barK Y :=
    funext (fun z => (normalized_kernel_identity Y hY z).symm)
  change HasDerivAt (fun z : ℂ => barH Y z+(2/3:ℂ)*z*deriv (barH Y) z) _ 1 at hp
  rw [he] at hp
  have hd := hp.deriv
  simp only [id_eq,mul_one] at hd
  rw [barH_deriv_one Y hY] at hd
  have hr := congrArg Complex.re hd
  norm_num [Complex.add_re,Complex.mul_re] at hr
  have hkn : deriv (barK Y) 1≠0 := by
    have hz := Analysis.deflatedBarK_zero_free_unit Y hY 1 (by norm_num)
    intro hh
    apply hz
    rw [Analysis.deflatedBarK_one,hh,neg_zero]
  have hkr : (deriv (barK Y) 1).re≠0 := by
    intro hh
    apply hkn
    apply Complex.ext
    · exact hh
    · exact Analysis.barK_deriv_one_real Y
  have ht : Theta Y*(deriv (barK Y) 1).re = -1 := by
    rw [Theta,Analysis.theta_sum_kernel_deriv Y hY]
    field_simp
  dsimp only [A]
  nlinarith [congrArg (fun x : ℝ => Theta Y*x) hr]

lemma canonicalDilaton_degreeCorrection_hasSum (p : ℕ) (Y : ℝ) (hY : Y ∈ Set.Icc (0:ℝ) y₀) :
    HasSum (fun d : ℕ => canonicalDilatonCoefficient Y d*degreeCorrection (d::List.replicate p 0) Y)
      (A Y*(A Y*(((7-2*(p:ℝ))/4)*Theta Y-moment₁ Y+2-p)-1/2)) := by
  have hs := canonicalDilaton_degreeCorrection_hasSum_raw p Y hY
  have he := barH_second_theta_identity Y hY
  convert! hs using 1
  nlinarith [congrArg (fun x : ℝ => A Y*x) he]
end WP
