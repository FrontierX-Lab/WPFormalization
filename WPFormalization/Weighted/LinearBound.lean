import WPFormalization.Weighted.LayerBudget
import WPFormalization.Weighted.LinearMass
import WPFormalization.Analysis.LinearMassBounds

/-! The actual weighted linear estimate; the last uniform square-root bound uses the proved uniform mass theorem H22. -/
noncomputable section
namespace WP
lemma weightedLinearLayer_zero_zero (c : ℝ) (d : List ℕ) (hd : ∀ k ∈ d, k=0) :
    weightedLinearLayer c 0 d 0 = 0 := by
  unfold weightedLinearLayer
  norm_num only [Nat.zero_add,Nat.zero_sub,Finset.range_zero,Finset.sum_empty,mul_zero,add_zero]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hv : d[j]! = 0 := by
    apply hd
    simpa [hj'] using (List.getElem_mem (l := d) j hj')
  simp [hv]
lemma list_sum_zero_of_entries (d : List ℕ) (hd : ∀ k ∈ d, k=0) : d.sum=0 := by
  induction d with
  | nil => rfl
  | cons k d ih =>
    have hk := hd k (by simp)
    have hh := ih (fun j hj => hd j (by simp [hj]))
    simp [hk,hh]
lemma coarse_weighted_mass (S h : ℝ) (hS : 0 ≤ S) (hh : 2 ≤ h) :
    1+2048*S/(3*(h-1)) ≤ 1+4096*S/h := by
  have hden : 0 < 3*(h-1) := by linarith
  have hh₀ : 0 < h := by linarith
  have hc : (2048 : ℝ)/(3*(h-1)) ≤ 4096/h := by
    apply (div_le_div_iff₀ hden hh₀).mpr
    nlinarith
  have he := mul_le_mul_of_nonneg_right hc hS
  nlinarith [show (2048 : ℝ)*S/(3*(h-1)) = (2048/(3*(h-1)))*S by ring,
    show (4096 : ℝ)*S/h = (4096/h)*S by ring]
lemma weightedLinear_finite_bound (c Y : ℝ) (hc : 0 < c) (hsmall : c ≤ 1/64)
    (g pivot : ℕ) (d : List ℕ) (hg : 2 ≤ g) (hchoice : PivotChoice pivot d)
    (hd : (pivot :: d).sum ≤ dimension g (d.length+1)) (hY : Y ∈ Set.Icc 0 y₀) :
    weightedLinear c Y g pivot d ≤
      1+4096*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))/complexity g (d.length+1) := by
  let h := complexity g (d.length+1)
  let m := deficit g (pivot :: d)
  let den : ℝ := 3*((h : ℝ)-1)
  have hh : 2 ≤ h := by dsimp only [h]; unfold complexity; omega
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hden : 0 < den := by dsimp only [den]; linarith
  have hq (l : ℕ) : 0 ≤ linearQ Y h m l/den :=
    div_nonneg (linearQ_nonneg Y hY h m l hh) hden.le
  have heq : weightedLinear c Y g pivot d =
      ∑ l ∈ Finset.range (m+1), (linearQ Y h m l/den)*weightedLinearLayer c pivot d l :=
    weightedLinear_eq_layers c Y g pivot d hg hd hY
  have hsumq : (∑ l ∈ Finset.range (m+1), linearQ Y h m l/den) = linearS₀ Y h m/den := by
    rw [← Finset.sum_div]
    rfl
  apply le_trans (b := 1+2048*linearS₀ Y h m/den)
  · by_cases hp : pivot=0
    · subst pivot
      have hzero : ∀ k ∈ d, k=0 := by
        unfold PivotChoice at hchoice
        rcases hchoice with hbad | ⟨hbad,_⟩ | ⟨_,hz⟩
        · omega
        · omega
        · exact hz
      have hsum := list_sum_zero_of_entries d hzero
      have hmdim : m = dimension g (d.length+1) := by
        dsimp only [m,deficit]
        simp only [List.sum_cons,List.length_cons,zero_add,hsum,Nat.sub_zero]
      let U := fun l : ℕ => (d.length : ℝ)*(if 1≤l then 1 else 0)+2*(l-1 : ℕ)
      have hLayer (l : ℕ) : weightedLinearLayer c 0 d l ≤ U l+2048*(if 1≤l then 1 else 0) := by
        by_cases hl : l=0
        · subst l
          rw [weightedLinearLayer_zero_zero c d hzero]
          norm_num [U]
        · have hl' : 1≤l := by omega
          simpa only [U,hl',ite_true,mul_one] using weightedLinearLayer_zero_bound c hc hsmall d hzero l hl'
      have hmass : (∑ l ∈ Finset.range (m+1), linearQ Y h m l/den*U l) = zeroLinearMass Y g (d.length+1) := by
        unfold zeroLinearMass
        dsimp only
        rw [← hmdim]
        apply Finset.sum_congr rfl
        intro l hl
        dsimp only [U,den,h]
        simp only [Nat.cast_add,Nat.cast_one]
        ring
      have htail : (∑ l ∈ Finset.range (m+1), linearQ Y h m l/den*(if 1≤l then 1 else 0)) =
          (linearS₀ Y h m-linearQ Y h m 0)/den := by
        rw [Finset.sum_range_succ']
        simp only [show ¬(1≤(0:ℕ)) by decide,ite_false,mul_zero,add_zero,
          (show ∀ i : ℕ, 1 ≤ i + 1 from fun i => by omega),ite_true,mul_one]
        rw [← Finset.sum_div,← linearS₀_tail]
      have hbound : weightedLinear c Y g 0 d ≤
          zeroLinearMass Y g (d.length+1)+2048*(linearS₀ Y h m-linearQ Y h m 0)/den := by
        rw [heq]
        calc
          _ ≤ ∑ l ∈ Finset.range (m+1), (linearQ Y h m l/den)*(U l+2048*(if 1≤l then 1 else 0)) := by
            apply Finset.sum_le_sum
            intro l hl
            exact mul_le_mul_of_nonneg_left (hLayer l) (hq l)
          _ = _ := by
            simp only [mul_add,Finset.sum_add_distrib]
            rw [hmass]
            have ht : (∑ l ∈ Finset.range (m+1), (linearQ Y h m l/den)*(2048*(if 1≤l then 1 else 0))) =
                2048*(∑ l ∈ Finset.range (m+1), (linearQ Y h m l/den)*(if 1≤l then 1 else 0)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro l hl
              ring
            rw [ht,htail]
            ring
      have hmass0 := zeroLinearMass_le_q₀ Y hY g (d.length+1) hg (by omega)
      rw [← hmdim] at hmass0
      change zeroLinearMass Y g (d.length+1) ≤ 1+2*linearQ Y h m 0/den at hmass0
      have hq0 : 0 ≤ linearQ Y h m 0 := linearQ_nonneg Y hY h m 0 hh
      have hpen : 0 ≤ 2046*linearQ Y h m 0/den := by positivity
      have halgebra : 1+2*linearQ Y h m 0/den+2048*(linearS₀ Y h m-linearQ Y h m 0)/den =
          1+2048*linearS₀ Y h m/den-2046*linearQ Y h m 0/den := by ring
      linarith
    · have hp' : 1 ≤ pivot := by omega
      have hmass := linear_count_mass Y hY g pivot d hg hp' hd
      have hbound : weightedLinear c Y g pivot d ≤
          ∑ l ∈ Finset.range (m+1), (linearQ Y h m l/den)*
            ((∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1))+2*(pivot+l-1 : ℕ)+2048) := by
        rw [heq]
        apply Finset.sum_le_sum
        intro l hl
        exact mul_le_mul_of_nonneg_left (weightedLinearLayer_positive_bound c hc hsmall pivot hp' d l) (hq l)
      have hsum : (∑ l ∈ Finset.range (m+1), (linearQ Y h m l/den)*
            ((∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1))+2*(pivot+l-1 : ℕ)+2048)) =
          1+2048*linearS₀ Y h m/den := by
        have hmass' : (∑ l ∈ Finset.range (m+1),
            (linearQ Y h m l/den)*((∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1))+2*(pivot+l-1 : ℕ))) = 1 := hmass
        calc
          _ = (∑ l ∈ Finset.range (m+1), (linearQ Y h m l/den)*
              ((∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1))+2*(pivot+l-1 : ℕ))) +
              (∑ l ∈ Finset.range (m+1), (linearQ Y h m l/den)*2048) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro l hl
            ring
          _ = _ := by
            rw [hmass',← Finset.sum_mul,hsumq]
            ring
      exact hbound.trans hsum.le
  · exact coarse_weighted_mass (linearS₀ Y h m) h (linearS₀_nonneg Y hY h m hh) hhR
lemma scalar_linear_sqrt_envelope (S h A C : ℝ) (hh : 0 < h) (hA : 0 ≤ A)
    (hS : S ≤ C*Real.sqrt h) : 1+A*S/h ≤ 1+(A*C)/Real.sqrt h := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos_of_pos hh
  apply add_le_add_right
  apply (div_le_div_iff₀ hh hs).mpr
  calc
    _ = (A*Real.sqrt h)*S := by ring
    _ ≤ (A*Real.sqrt h)*(C*Real.sqrt h) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = A*C*(Real.sqrt h)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hh.le]
theorem weighted_linear_bound_core : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c ∈ Set.Ioc 0 c₀,
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ g pivot : ℕ, ∀ d : List ℕ,
      PivotChoice pivot d → ¬ Terminal g (pivot :: d) →
      (pivot :: d).sum ≤ dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
        weightedLinear c Y g pivot d ≤
          1+C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))/complexity g (d.length+1) ∧
        1+C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))/complexity g (d.length+1) ≤
          1+C₂/Real.sqrt (complexity g (d.length+1)) := by
  obtain ⟨C,hC,hMass⟩ := linear_mass_bounds
  refine ⟨1/64,by norm_num,?_⟩
  intro c hc
  refine ⟨4096,4096*C,by norm_num,by positivity,?_⟩
  intro g pivot d hp hNt hd Y hY
  have hg : 2 ≤ g := by
    unfold Terminal at hNt
    push_neg at hNt
    omega
  have hh : 2 ≤ complexity g (d.length+1) := by unfold complexity; omega
  refine ⟨weightedLinear_finite_bound c Y hc.1 hc.2 g pivot d hg hp hd hY,?_⟩
  have hm := (hMass g (pivot :: d) (by simpa only [List.length_cons] using hh)
    (by simp) (by simpa only [List.length_cons] using hd) Y hY).1
  have hhR : (0 : ℝ) < complexity g (d.length+1) := by exact_mod_cast (show 0 < complexity g (d.length+1) by omega)
  exact scalar_linear_sqrt_envelope _ _ 4096 C hhR (by norm_num) hm
end WP
