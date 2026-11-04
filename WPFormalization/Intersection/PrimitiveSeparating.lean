import WPFormalization.Intersection.PrimitiveLower
import WPFormalization.Intersection.PrimitiveSeparatingWeight
/-! Actual separating DVV contributions, controlled by the complete factorial
weight sum. Dimension compatibility gives a unique node degree per genus and
subset; genus-zero terms vanish for external degrees at least two. The remaining
upper-bound premise is precisely the lower-complexity child bound of the intended
strong induction; no bound is added to PsiTheory. -/
noncomputable section
namespace WP
lemma selected_ge_two (d : List ℤ) (hd : ∀ k ∈ d, 2 ≤ k) (I : Finset ℕ) :
    ∀ k ∈ selected d I, 2 ≤ k := by
  intro k hk
  unfold selected at hk
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
  have hj' := (List.mem_filter.mp hj).1
  have hjn : j < d.length := List.mem_range.mp hj'
  apply hd
  simpa [hjn] using (List.getElem_mem (l := d) j hjn)
lemma selected_length_card (d : List ℤ) (I : Finset ℕ)
    (hI : I ⊆ Finset.range d.length) : (selected d I).length = I.card := by
  have he : ((List.range d.length).filter (fun i => i ∈ I)).toFinset = I := by
    ext j
    simp only [List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq]
    constructor
    · intro hj; exact hj.2
    · intro hj; exact ⟨Finset.mem_range.mp (hI hj),hj⟩
  have hn := List.toFinset_card_of_nodup ((List.nodup_range : (List.range d.length).Nodup).filter (fun i => decide (i ∈ I)))
  unfold selected
  simp only [List.length_map]
  rw [← hn,he]
lemma signedPureC_genus_zero_tail (P : PsiTheory) (u : ℤ) (d : List ℤ)
    (hu : 0 ≤ u) (hd : ∀ k ∈ d, 2 ≤ k) : signedPureC P 0 (u :: d) = 0 := by
  have hsum := twice_length_le_sum d hd
  apply signedPureC_vanish P 0 (u :: d)
  right; right
  simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,Nat.cast_zero,mul_zero]
  omega
lemma nonnegative_node_count (u : ℤ) (d : List ℤ) (hd : ∀ k ∈ d, 2 ≤ k) :
    (u :: d).count 0 ≤ 1 := by
  have hz : d.count 0 = 0 := List.count_eq_zero.mpr
    (fun hm => by have := hd 0 hm; omega)
  simp only [List.count_cons,hz]
  split_ifs <;> omega
/-- Exact normalized separating summand, with its actual psi-derived factors. -/
def primitiveSeparatingTerm (P : PsiTheory) (g pivot : ℕ) (d : List ℤ)
    (u g₁ : ℕ) (I : Finset ℕ) : ℝ :=
  let c₁ := (u : ℤ) :: selected d I
  let c₂ := ((pivot : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)
  (Real.Gamma (complexity g₁ c₁.length) * Real.Gamma (complexity (g-g₁) c₂.length) /
    (6*Real.Gamma (complexity g (d.length+1)))) *
    signedPureC P g₁ c₁ * signedPureC P (g-g₁) c₂
lemma primitiveSeparatingTerm_zero_genus (P : PsiTheory) (g pivot : ℕ) (d : List ℤ)
    (hd : ∀ k ∈ d, 2 ≤ k) (u : ℕ) (hu : u ∈ Finset.range (pivot-1))
    (g₁ : ℕ) (hz : g₁ = 0 ∨ g-g₁ = 0) (I : Finset ℕ) :
    primitiveSeparatingTerm P g pivot d u g₁ I = 0 := by
  unfold primitiveSeparatingTerm
  dsimp only
  rcases hz with hz | hz
  · rw [hz,signedPureC_genus_zero_tail P u (selected d I) (by positivity)
      (selected_ge_two d hd I)]
    ring
  · have hu' := Finset.mem_range.mp hu
    rw [hz,signedPureC_genus_zero_tail P ((pivot : ℤ)-2-u)
      (selected d ((Finset.range d.length) \ I)) (by omega)
      (selected_ge_two d hd _)]
    ring
def primitiveSeparatingCoefficient (g : ℕ) (d : List ℤ) (g₁ : ℕ) (I : Finset ℕ) : ℝ :=
  (Real.Gamma (complexity g₁ ((selected d I).length+1)) *
    Real.Gamma (complexity (g-g₁) ((selected d ((Finset.range d.length) \ I)).length+1)) /
      (6*Real.Gamma (complexity g (d.length+1))))
lemma primitiveSeparatingTerm_dim_zero (P : PsiTheory) (g pivot : ℕ) (d : List ℤ)
    (u g₁ : ℕ) (I : Finset ℕ)
    (hdim : ((u : ℤ) :: selected d I).sum ≠
      3*(g₁ : ℤ)-3+((u : ℤ) :: selected d I).length) :
    primitiveSeparatingTerm P g pivot d u g₁ I = 0 := by
  unfold primitiveSeparatingTerm
  dsimp only
  rw [signedPureC_vanish P g₁ ((u : ℤ) :: selected d I) (Or.inr (Or.inr hdim))]
  ring
lemma primitiveSeparating_sum_u_le (P : PsiTheory) (g pivot : ℕ) (d : List ℤ)
    (hd : ∀ k ∈ d, 2 ≤ k)
    (hdim : ((pivot : ℤ) :: d).sum = 3*(g : ℤ)-3+(d.length+1))
    (g₁ : ℕ) (hg₁ : 1 ≤ g₁) (hg₂ : g₁ < g) (I : Finset ℕ)
    (hupp : ∀ g' c, 1 ≤ g' → Stable g' c.length → (∀ k ∈ c, 0 ≤ k) →
      c.count 0 ≤ 1 → c.sum = 3*(g' : ℤ)-3+c.length →
      complexity g' c.length < complexity g (d.length+1) → signedPureC P g' c ≤ 1) :
    (∑ u ∈ Finset.range (pivot-1), primitiveSeparatingTerm P g pivot d u g₁ I) ≤
      primitiveSeparatingCoefficient g d g₁ I := by
  have hcoef : 0 ≤ primitiveSeparatingCoefficient g d g₁ I := by
    unfold primitiveSeparatingCoefficient
    exact div_nonneg (mul_nonneg (gamma_nat_nonneg _) (gamma_nat_nonneg _))
      (mul_nonneg (by norm_num) (gamma_nat_nonneg _))
  by_cases hex : ∃ u ∈ Finset.range (pivot-1), ((u : ℤ) :: selected d I).sum =
      3*(g₁ : ℤ)-3+((u : ℤ) :: selected d I).length
  · obtain ⟨u₀,hu₀,hdim₀⟩ := hex
    rw [Finset.sum_eq_single u₀]
    · let c₁ := (u₀ : ℤ) :: selected d I
      let c₂ := ((pivot : ℤ)-2-u₀) :: selected d ((Finset.range d.length) \ I)
      have hu₀' := Finset.mem_range.mp hu₀
      have hmin₁ := selected_ge_two d hd I
      have hmin₂ := selected_ge_two d hd ((Finset.range d.length) \ I)
      have hl := selected_partition_length d I
      have hst₁ : Stable g₁ c₁.length := by dsimp only [c₁]; simp only [Stable,List.length_cons]; omega
      have hst₂ : Stable (g-g₁) c₂.length := by dsimp only [c₂]; simp only [Stable,List.length_cons]; omega
      have hc₁ : complexity g₁ c₁.length < complexity g (d.length+1) := by
        dsimp only [c₁]
        simp only [complexity,List.length_cons]
        omega
      have hc₂ : complexity (g-g₁) c₂.length < complexity g (d.length+1) := by
        dsimp only [c₂]
        simp only [complexity,List.length_cons]
        omega
      have hnon₁ : ∀ k ∈ c₁, 0 ≤ k := by
        intro k hk
        rcases List.mem_cons.mp hk with hk | hk
        · subst k; positivity
        · have := hmin₁ k hk; omega
      have hnon₂ : ∀ k ∈ c₂, 0 ≤ k := by
        intro k hk
        rcases List.mem_cons.mp hk with hk | hk
        · subst k; omega
        · have := hmin₂ k hk; omega
      have hdim₂ : c₂.sum = 3*((g-g₁ : ℕ) : ℤ)-3+c₂.length := by
        have he := separating_dimension g g₁ (by omega) pivot d (by simpa using hdim) u₀ I
        dsimp only [c₁,c₂]
        rw [hdim₀] at he
        linarith
      have hC₁ := hupp g₁ c₁ hg₁ hst₁ hnon₁ (nonnegative_node_count _ _ hmin₁) hdim₀ hc₁
      have hC₂ := hupp (g-g₁) c₂ (by omega) hst₂ hnon₂ (nonnegative_node_count _ _ hmin₂) hdim₂ hc₂
      have hprod : signedPureC P g₁ c₁*signedPureC P (g-g₁) c₂ ≤ 1 := by
        calc
          _ ≤ 1*signedPureC P (g-g₁) c₂ :=
            mul_le_mul_of_nonneg_right hC₁ (signedPureC_nonneg P _ _)
          _ ≤ 1*1 := mul_le_mul_of_nonneg_left hC₂ (by norm_num)
          _ = 1 := by ring
      have he := mul_le_mul_of_nonneg_left hprod hcoef
      simpa only [primitiveSeparatingTerm,primitiveSeparatingCoefficient,
        List.length_cons,c₁,c₂,mul_assoc,mul_one] using he
    · intro u hu hne
      apply primitiveSeparatingTerm_dim_zero P g pivot d u g₁ I
      intro hdim'
      simp only [List.sum_cons,List.length_cons] at hdim₀ hdim'
      have huu : u = u₀ := by omega
      exact hne huu
    · intro hu
      exact (hu hu₀).elim
  · have hz : ∀ u ∈ Finset.range (pivot-1), primitiveSeparatingTerm P g pivot d u g₁ I = 0 := by
      intro u hu
      apply primitiveSeparatingTerm_dim_zero P g pivot d u g₁ I
      intro hdim'
      exact hex ⟨u,hu,hdim'⟩
    rw [Finset.sum_eq_zero hz]
    exact hcoef
lemma primitiveSeparatingCoefficient_factorial (g : ℕ) (d : List ℤ)
    (i : ℕ) (hi : i ∈ Finset.range (g-1)) (I : Finset ℕ)
    (hI : I ∈ (Finset.range d.length).powerset) :
    primitiveSeparatingCoefficient g d (i+1) I =
      ((2*i+I.card).factorial : ℝ)*(2*(g-2-i)+(d.length-I.card)).factorial /
        (6*(complexity g (d.length+1)-1).factorial) := by
  have hi' := Finset.mem_range.mp hi
  have hIs := Finset.mem_powerset.mp hI
  have hcard := Finset.card_le_card hIs
  simp only [Finset.card_range] at hcard
  have hlen₁ := selected_length_card d I hIs
  have hpart := selected_partition_length d I
  have hlen₂ : (selected d ((Finset.range d.length) \ I)).length = d.length-I.card := by omega
  have hc₁ : complexity (i+1) (I.card+1) = (2*i+I.card)+1 := by unfold complexity; omega
  have hc₂ : complexity (g-(i+1)) (d.length-I.card+1) =
      (2*(g-2-i)+(d.length-I.card))+1 := by unfold complexity; omega
  have hc : complexity g (d.length+1) = (complexity g (d.length+1)-1)+1 := by unfold complexity; omega
  unfold primitiveSeparatingCoefficient
  rw [hlen₁,hlen₂,hc₁,hc₂]
  rw [show Real.Gamma (complexity g (d.length+1)) =
      ((complexity g (d.length+1)-1).factorial : ℝ) by
    nth_rw 1 [hc]; rw [Nat.cast_add,Nat.cast_one,Real.Gamma_nat_eq_factorial]]
  rw [Nat.cast_add,Nat.cast_one,Real.Gamma_nat_eq_factorial,
    Nat.cast_add,Nat.cast_one,Real.Gamma_nat_eq_factorial]
lemma primitiveSeparatingCoefficient_sum (g : ℕ) (d : List ℤ) :
    (∑ i ∈ Finset.range (g-1), ∑ I ∈ (Finset.range d.length).powerset,
      primitiveSeparatingCoefficient g d (i+1) I) =
      primitiveSeparatingWeight g (d.length+1) := by
  unfold primitiveSeparatingWeight
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ I ∈ (Finset.range d.length).powerset,
        ((2*i+I.card).factorial : ℝ)*(2*(g-2-i)+(d.length-I.card)).factorial /
          (6*(complexity g (d.length+1)-1).factorial) := by
      apply Finset.sum_congr rfl
      intro I hI
      exact primitiveSeparatingCoefficient_factorial g d i hi I hI
    _ = _ := by
      have he := Finset.sum_powerset_apply_card
        (fun m => ((2*i+m).factorial : ℝ)*(2*(g-2-i)+(d.length-m)).factorial /
          (6*(complexity g (d.length+1)-1).factorial)) (x := Finset.range d.length)
      simp only [Finset.card_range,nsmul_eq_mul] at he
      rw [he]
      apply Finset.sum_congr rfl
      intro m hm
      ring
lemma sum_middle_genus (g : ℕ) (hg : 1 ≤ g) (F : ℕ → ℝ) :
    (∑ g₁ ∈ Finset.range (g+1), if 1 ≤ g₁ ∧ g₁ < g then F g₁ else 0) =
      ∑ i ∈ Finset.range (g-1), F (i+1) := by
  rw [Finset.sum_range_succ]
  have he : g = (g-1)+1 := by omega
  nth_rw 1 [he]
  rw [Finset.sum_range_succ']
  simp only [show ¬ (1 ≤ g ∧ g < g) by omega,
    show ¬ (1 ≤ 0 ∧ 0 < g) by omega,ite_false,add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [if_pos (by omega)]
/-- The actual separating contribution is bounded by the complete weight sum,
assuming exactly the lower-complexity upper bounds used in the induction. -/
lemma primitiveSeparating_le_weight (P : PsiTheory) (g pivot : ℕ) (d : List ℤ)
    (hg : 2 ≤ g) (hd : ∀ k ∈ d, 2 ≤ k)
    (hdim : ((pivot : ℤ) :: d).sum = 3*(g : ℤ)-3+(d.length+1))
    (hupp : ∀ g' c, 1 ≤ g' → Stable g' c.length → (∀ k ∈ c, 0 ≤ k) →
      c.count 0 ≤ 1 → c.sum = 3*(g' : ℤ)-3+c.length →
      complexity g' c.length < complexity g (d.length+1) → signedPureC P g' c ≤ 1) :
    (∑ u ∈ Finset.range (pivot-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        primitiveSeparatingTerm P g pivot d u g₁ I) ≤
      primitiveSeparatingWeight g (d.length+1) := by
  calc
    _ = ∑ g₁ ∈ Finset.range (g+1), ∑ I ∈ (Finset.range d.length).powerset,
        ∑ u ∈ Finset.range (pivot-1), primitiveSeparatingTerm P g pivot d u g₁ I := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g₁ hg₁
      rw [Finset.sum_comm]
    _ ≤ ∑ g₁ ∈ Finset.range (g+1), if 1 ≤ g₁ ∧ g₁ < g then
        (∑ I ∈ (Finset.range d.length).powerset,
          primitiveSeparatingCoefficient g d g₁ I) else 0 := by
      apply Finset.sum_le_sum
      intro g₁ hg₁
      by_cases hmid : 1 ≤ g₁ ∧ g₁ < g
      · rw [if_pos hmid]
        apply Finset.sum_le_sum
        intro I hI
        exact primitiveSeparating_sum_u_le P g pivot d hd hdim g₁ hmid.1 hmid.2 I hupp
      · rw [if_neg hmid]
        have hz : g₁ = 0 ∨ g-g₁ = 0 := by
          have hrg := Finset.mem_range.mp hg₁
          omega
        have heq : (∑ I ∈ (Finset.range d.length).powerset,
            ∑ u ∈ Finset.range (pivot-1), primitiveSeparatingTerm P g pivot d u g₁ I) = 0 := by
          apply Finset.sum_eq_zero
          intro I hI
          apply Finset.sum_eq_zero
          intro u hu
          exact primitiveSeparatingTerm_zero_genus P g pivot d hd u hu g₁ hz I
        exact heq.le
    _ = _ := by
      rw [sum_middle_genus g (by omega)]
      exact primitiveSeparatingCoefficient_sum g d
lemma primitiveSeparating_bound (P : PsiTheory) (g pivot : ℕ) (d : List ℤ)
    (hg : 2 ≤ g) (hd : ∀ k ∈ (pivot : ℤ) :: d, 2 ≤ k)
    (hdim : ((pivot : ℤ) :: d).sum = 3*(g : ℤ)-3+(d.length+1))
    (hupp : ∀ g' c, 1 ≤ g' → Stable g' c.length → (∀ k ∈ c, 0 ≤ k) →
      c.count 0 ≤ 1 → c.sum = 3*(g' : ℤ)-3+c.length →
      complexity g' c.length < complexity g (d.length+1) → signedPureC P g' c ≤ 1) :
    (∑ u ∈ Finset.range (pivot-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        primitiveSeparatingTerm P g pivot d u g₁ I) ≤
      2/(((complexity g (d.length+1) : ℝ)-1)*((complexity g (d.length+1) : ℝ)-2)) := by
  have hsum := twice_length_le_sum ((pivot : ℤ) :: d) hd
  have hnmax : d.length+1 ≤ 3*g-3 := by
    simp only [List.length_cons] at hsum
    omega
  exact (primitiveSeparating_le_weight P g pivot d hg
    (fun k hk => hd k (by simp [hk])) hdim hupp).trans
    (primitiveSeparatingWeight_bound g (d.length+1) hg (by omega) hnmax)
end WP
