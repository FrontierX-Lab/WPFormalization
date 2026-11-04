import WPFormalization.Weighted.CoefficientConvolution

/-! Exact unweighted linear mass, including the all-zero pivot correction. -/
noncomputable section
namespace WP
lemma sum_degree_weights (d : List ℕ) :
    (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)) = 2*(d.sum : ℝ)+d.length := by
  induction d with
  | nil => simp
  | cons k d ih =>
    simp only [List.length_cons,Finset.sum_range_succ',List.getElem!_cons_zero,
      List.getElem!_cons_succ,ih,List.sum_cons,Nat.cast_add,Nat.cast_one]
    ring
lemma linear_count_mass (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (g pivot : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (hp : 1 ≤ pivot) (hd : (pivot :: d).sum ≤ dimension g (d.length+1)) :
    (∑ l ∈ Finset.range (deficit g (pivot :: d)+1),
      (linearQ Y (complexity g (d.length+1)) (deficit g (pivot :: d)) l /
        (3*((complexity g (d.length+1) : ℝ)-1)))*
          ((∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1))+2*(pivot+l-1 : ℕ))) = 1 := by
  let h := complexity g (d.length+1)
  let m := deficit g (pivot :: d)
  have hh : 2 ≤ h := by dsimp only [h]; unfold complexity; omega
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hden : (0 : ℝ) < 3*((h : ℝ)-1) := by linarith
  have hs : Stable g (pivot :: d).length := by unfold Stable; omega
  have hm : (m : ℝ) = 3*(g : ℝ)-3+(d.length+1)-((pivot :: d).sum : ℝ) := by
    dsimp only [m,deficit]
    simp only [List.length_cons]
    rw [Nat.cast_sub hd]
    unfold dimension
    rw [Nat.cast_sub (by omega)]
    norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    ring
  have hc : (h : ℝ) = 2*(g : ℝ)+d.length-1 := by
    dsimp only [h]
    unfold complexity
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hpoint (l : ℕ) :
      ((∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1))+2*(pivot+l-1 : ℕ))/(3*((h : ℝ)-1)) =
        1-2*((m : ℝ)-l)/(3*((h : ℝ)-1)) := by
    rw [sum_degree_weights,Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]
    field_simp [show (h : ℝ)-1 ≠ 0 by linarith]
    simp only [List.sum_cons,Nat.cast_add] at hm
    rw [hc]
    nlinarith [hm]
  change (∑ l ∈ Finset.range (m+1), _) = 1
  calc
    _ = ∑ l ∈ Finset.range (m+1), linearQ Y h m l*(1-2*((m : ℝ)-l)/(3*((h : ℝ)-1))) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [show linearQ Y h m l/(3*((h : ℝ)-1))*
          ((∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1))+2*(pivot+l-1 : ℕ)) =
          linearQ Y h m l*(((∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1))+2*(pivot+l-1 : ℕ))/(3*((h : ℝ)-1))) by ring,
        hpoint]
    _ = 1 := mass_identity Y h m hh hY
lemma zeroLinearMass_le_q₀ (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (g n : ℕ)
    (hg : 2 ≤ g) (hn : 1 ≤ n) :
    zeroLinearMass Y g n ≤ 1+2*linearQ Y (complexity g n) (dimension g n) 0/
      (3*((complexity g n : ℝ)-1)) := by
  have hh : 2 ≤ complexity g n := by unfold complexity; omega
  have hhR : (2 : ℝ) ≤ complexity g n := by exact_mod_cast hh
  have hden : (0 : ℝ) < 3*((complexity g n : ℝ)-1) := by linarith
  rw [zero_mass_defect Y g n hg hn hY]
  have hQ : harmonicCoeff Y (complexity g n-1) (dimension g n)/harmonicCoeff Y (complexity g n) (dimension g n) =
      linearQ Y (complexity g n) (dimension g n) 0 := by
    unfold linearQ
    rw [theta_zero_closed Y hY]
    simp
  have hq : 0 ≤ linearQ Y (complexity g n) (dimension g n) 0 := linearQ_nonneg Y hY _ _ _ hh
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : (3-(n : ℝ))/(3*((complexity g n : ℝ)-1))*
      harmonicCoeff Y (complexity g n-1) (dimension g n)/harmonicCoeff Y (complexity g n) (dimension g n) =
      ((3-(n : ℝ))/(3*((complexity g n : ℝ)-1)))*linearQ Y (complexity g n) (dimension g n) 0 := by rw [← hQ]; ring
  rw [he]
  have hcoef : (3-(n : ℝ))/(3*((complexity g n : ℝ)-1)) ≤ 2/(3*((complexity g n : ℝ)-1)) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  have he' := mul_le_mul_of_nonneg_right hcoef hq
  nlinarith [show 2*linearQ Y (complexity g n) (dimension g n) 0/(3*((complexity g n : ℝ)-1)) =
    (2/(3*((complexity g n : ℝ)-1)))*linearQ Y (complexity g n) (dimension g n) 0 by ring]

end WP
