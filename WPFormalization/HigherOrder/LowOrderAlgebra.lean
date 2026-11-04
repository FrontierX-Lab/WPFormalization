import WPFormalization.HigherOrder.Coherence

/-! Exact low-order formal algebra and the first genus-ratio coefficient.
The genus identity for p≥2 follows from the actual triangular rule and the
proved three-point initial amplitude. It inherits the kernel moment dependency
of `profileCoefficient_one`, but assumes no genus coefficient formula.
-/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

lemma coeff_two_mul (f g : Series) :
    PowerSeries.coeff 2 (f*g) = PowerSeries.coeff 2 f*constantCoeff g +
      PowerSeries.coeff 1 f*PowerSeries.coeff 1 g+constantCoeff f*PowerSeries.coeff 2 g := by
  rw [PowerSeries.coeff_mul]
  have h : Finset.HasAntidiagonal.antidiagonal (2:ℕ) = {(0,2),(1,1),(2,0)} := rfl
  rw [h]
  simp [coeff_zero_eq_constantCoeff]
  ring

lemma finiteExp_two (f : Series) (hf : constantCoeff f = 0) :
    PowerSeries.coeff 2 (finiteExp f) = PowerSeries.coeff 2 f+(PowerSeries.coeff 1 f)^2/2 := by
  simp only [finiteExp,coeff_mk,Finset.sum_range_succ,Finset.sum_range_zero,
    pow_zero,pow_one,Nat.factorial_zero,Nat.factorial_one]
  norm_num only [PowerSeries.coeff_one,OfNat.ofNat_ne_zero,if_false,zero_add,one_div,
    Nat.factorial_succ,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_one,div_one]
  rw [pow_two,coeff_two_mul,hf]
  ring

lemma coeff_two_inv_unit (f : Series) (hf : constantCoeff f = 1) :
    PowerSeries.coeff 2 f⁻¹ = (PowerSeries.coeff 1 f)^2-PowerSeries.coeff 2 f := by
  rw [PowerSeries.coeff_inv]
  have h : Finset.HasAntidiagonal.antidiagonal (2:ℕ) = {(0,2),(1,1),(2,0)} := rfl
  rw [h]
  simp [hf,coeff_zero_eq_constantCoeff,coeff_one_inv_unit f hf]
  ring

/-- The actual first transport coefficient is c₁²−c₂ of the constructed cusp series. -/
lemma transportCoefficient_one_algebra (P : PsiTheory) (p : ℕ) (Y : ℝ) :
    transportCoefficient P p 1 Y = (cuspCoefficient P Y p 1)^2-cuspCoefficient P Y p 2 := by
  unfold transportCoefficient
  norm_num only [Nat.reduceAdd]
  rw [coeff_two_inv_unit _ (formalCusp_constant P Y p)]
  simp [formalCusp]

lemma markedCoefficient_two (P : PsiTheory) (p : ℕ) (Y : ℝ) :
    markedCoefficient P p 2 Y = logarithmicMarkedCoefficient P p 2 Y+
      (logarithmicMarkedCoefficient P p 1 Y)^2/2 := by
  unfold markedCoefficient
  rw [finiteExp_two _ (markedLogSeries_constant P p Y)]
  simp [markedLogSeries]

lemma ratioSeries_one_base (Y : ℝ) (p : ℕ) :
    PowerSeries.coeff 1 (ratioSeries Y baseJet p 0 1) = A Y := by
  simp [ratioSeries,baseJet,PowerSeries.coeff_one_mul]

lemma genusSeries_one (P : PsiTheory) (Y : ℝ) (profiles : List ℕ → Series)
    (p : ℕ) (hp : 2 ≤ p) :
    PowerSeries.coeff 1 (genusSeries P Y baseJet profiles 1 p) =
      PowerSeries.coeff 1 (profiles (1 :: List.replicate (p-1) 0)) -
        3*((p-2:ℕ):ℝ)*smallW P Y 0 [0,0,0]*A Y := by
  have h₁ (s : ℕ) : ¬ (Stable 1 (s+2) ∧ 1 ≤ 2*1+s ∧ 2*1+s ≤ 1) := by omega
  have h₀ (s : ℕ) : (Stable 0 (s+2) ∧ 1 ≤ 2*0+s ∧ 2*0+s ≤ 1) ↔ s = 1 := by
    simp only [Stable]
    omega
  unfold genusSeries
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,h₁,ite_false,
    Finset.sum_const_zero,add_zero,h₀]
  have hs : (∑ s ∈ Finset.range (p-1), if s = 1 then
      C ((Nat.choose (p-2) s:ℝ)*smallW P Y 0 (List.replicate (s+2) 0))*ratioSeries Y baseJet p 0 s else 0) =
      C (((p-2:ℕ):ℝ)*smallW P Y 0 [0,0,0])*ratioSeries Y baseJet p 0 1 := by
    by_cases hp₂ : p = 2
    · subst p
      simp
    · have hmem : 1 < p-1 := by omega
      simp [Finset.mem_range,hmem]
  have hr₀ : constantCoeff (ratioSeries Y baseJet p 0 1) = 0 := by simp [ratioSeries]
  rw [hs,map_sub,PowerSeries.coeff_one_mul]
  simp [PowerSeries.coeff_one_mul,ratioSeries_one_base,hr₀]
  ring

/-- At p≥2 the actual genus coefficient is −α_p, from the KdV finite rule. -/
lemma genusCoefficient_one_high (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀)
    (p : ℕ) (hp : 2 ≤ p) : genusCoefficient P Y p 1 = -alpha p Y := by
  have hp₀ : p ≠ 0 := by omega
  have hp₁ : p ≠ 1 := by omega
  let profiles := fun d => setCoeff (baseJet.profile d) 1 (profileAtOrder P Y baseJet 1 d)
  have he : genusCoefficient P Y p 1 = PowerSeries.coeff 1 (genusSeries P Y baseJet profiles 1 p) := by
    simp [genusCoefficient,hierarchyJet,nextJet,hp₀,hp₁,profiles]
  rw [he,genusSeries_one P Y profiles p hp]
  change PowerSeries.coeff 1 (setCoeff (baseJet.profile (1 :: List.replicate (p-1) 0)) 1
    (profileAtOrder P Y baseJet 1 (1 :: List.replicate (p-1) 0))) - _ = _
  rw [setCoeff_same,profileAtOrder_one P Y hY]
  have hw : smallW P Y 0 [0,0,0] = 1 := by
    simpa [smallW] using (initial_amplitudes P Y hY).1
  rw [hw]
  simp [degreeCorrection,alpha,Nat.cast_sub (by omega : 1 ≤ p),
    Nat.cast_sub (by omega : 2 ≤ p)]
  ring

lemma coeff_two_pow_zero (f : Series) (hf : constantCoeff f = 0) (n : ℕ) (hn : 3 ≤ n) :
    PowerSeries.coeff 2 (f^n) = 0 := by
  rcases n with _|_|_|n <;> try omega
  rw [pow_succ,coeff_two_mul]
  simp [hf,PowerSeries.coeff_one_pow]

lemma shiftVariable_two (c : ℝ) : PowerSeries.coeff 2 (shiftVariable c) = c := by
  unfold shiftVariable
  rw [coeff_two_mul]
  norm_num only [PowerSeries.coeff_X,constantCoeff_X,zero_mul,one_mul,zero_add,add_zero]
  have he : (1-C c*PowerSeries.X : Series) = 1+C (-c)*PowerSeries.X := by
    simp [sub_eq_add_neg]
  rw [he,coeff_one_linear_inv]
  simp

/-- Second-order complexity substitution, retaining the indispensable shift contribution. -/
lemma complexityShift_two (c : ℝ) (f : Series) :
    PowerSeries.coeff 2 (complexityShift c f) = PowerSeries.coeff 2 f+c*PowerSeries.coeff 1 f := by
  unfold complexityShift
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (shiftVariable_constant c))]
  have hsupport : Function.support (fun n : ℕ =>
      PowerSeries.coeff n f • PowerSeries.coeff 2 ((shiftVariable c)^n)) ⊆ (Finset.range 3 : Set ℕ) := by
    intro n hn
    by_contra hnot
    have hn₃ : 3 ≤ n := by simpa only [Finset.mem_coe,Finset.mem_range,not_lt] using hnot
    have hz := coeff_two_pow_zero (shiftVariable c) (shiftVariable_constant c) n hn₃
    simp only [Function.mem_support] at hn
    exact hn (by simp [hz])
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  norm_num [Finset.sum_range_succ,shiftVariable_two,pow_two,coeff_two_mul,shiftVariable_one]
  ring

end WP.HigherOrder
