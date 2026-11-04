import WPFormalization.Comparison.LinearLower
import WPFormalization.Weighted.Clipping
/-! The actual positive recursion after division by the harmonic model and the
clipped state weight. Linear and separating child caps are required only for
children with nonzero validModel. Signed invalid and unstable children therefore
contribute zero. This is a proved recurrence rule on the explicit PsiTheory
interface, with no new field or paper theorem assumed. -/
noncomputable section
namespace WP.Comparison
lemma signedWeight_pos (c : ℝ) (ds : List ℤ) : 0 < signedWeight c ds := clippedWeight_pos c _
lemma normInt_weighted_upper (P : PsiTheory) (c Y : ℝ) (g : ℕ) (ds : List ℤ) (L : ℝ)
    (hY : Y ∈ Set.Icc 0 y₀)
    (hchild : validModel g ds Y ≠ 0 → ratio P g (ds.map Int.toNat) Y/signedWeight c ds ≤ L) :
    normInt P g ds Y ≤ L*(validModel g ds Y*signedWeight c ds) := by
  rw [normInt_eq_validModel_mul_ratio P g ds Y hY]
  by_cases hv : validModel g ds Y=0
  · rw [hv]
    norm_num
  · have hr := (div_le_iff₀ (signedWeight_pos c ds)).mp (hchild hv)
    have he := mul_le_mul_of_nonneg_left hr (validModel_nonneg g ds Y hY)
    convert he using 1 <;> ring
lemma normInt_product_weighted_upper (P : PsiTheory) (c Y : ℝ) (g₁ g₂ : ℕ) (ds₁ ds₂ : List ℤ) (B : ℝ)
    (hY : Y ∈ Set.Icc 0 y₀)
    (hchild : validModel g₁ ds₁ Y ≠ 0 → validModel g₂ ds₂ Y ≠ 0 →
      (ratio P g₁ (ds₁.map Int.toNat) Y/signedWeight c ds₁)*
        (ratio P g₂ (ds₂.map Int.toNat) Y/signedWeight c ds₂) ≤ B) :
    normInt P g₁ ds₁ Y*normInt P g₂ ds₂ Y ≤
      B*(validModel g₁ ds₁ Y*validModel g₂ ds₂ Y*signedWeight c ds₁*signedWeight c ds₂) := by
  rw [normInt_eq_validModel_mul_ratio P g₁ ds₁ Y hY,normInt_eq_validModel_mul_ratio P g₂ ds₂ Y hY]
  by_cases hv₁ : validModel g₁ ds₁ Y=0
  · rw [hv₁]
    norm_num
  · by_cases hv₂ : validModel g₂ ds₂ Y=0
    · rw [hv₂]
      norm_num
    · have hw₁ := signedWeight_pos c ds₁
      have hw₂ := signedWeight_pos c ds₂
      have hr : ratio P g₁ (ds₁.map Int.toNat) Y*ratio P g₂ (ds₂.map Int.toNat) Y ≤
          B*(signedWeight c ds₁*signedWeight c ds₂) := by
        calc
          _ = ((ratio P g₁ (ds₁.map Int.toNat) Y/signedWeight c ds₁)*
              (ratio P g₂ (ds₂.map Int.toNat) Y/signedWeight c ds₂))*
                (signedWeight c ds₁*signedWeight c ds₂) := by field_simp [hw₁.ne',hw₂.ne'] <;> ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hchild hv₁ hv₂) (mul_nonneg hw₁.le hw₂.le)
      have he := mul_le_mul_of_nonneg_left hr
        (mul_nonneg (validModel_nonneg g₁ ds₁ Y hY) (validModel_nonneg g₂ ds₂ Y hY))
      convert he using 1 <;> ring

def linearSum (Y : ℝ) (g pivot : ℕ) (d : List ℕ) (f : ℕ → List ℤ → ℝ) : ℝ :=
  let m := deficit g (pivot::d)
  (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*
    ∑ l ∈ Finset.range (m+1), theta Y l*f g
      (((pivot : ℤ)+d[j]!+l-1)::(d.eraseIdx j).map Int.ofNat))+
  (if g=0 then 0 else (1/2 : ℝ)*∑ l ∈ Finset.range (m+1), theta Y l*
    ∑ u ∈ Finset.range (pivot+l-1), f (g-1)
      ((u : ℤ)::((pivot : ℤ)+l-2-u)::d.map Int.ofNat))
def separatingSum (Y : ℝ) (g pivot : ℕ) (d : List ℕ)
    (f : ℕ → List ℤ → ℕ → List ℤ → ℝ) : ℝ :=
  let m := deficit g (pivot::d)
  (1/2 : ℝ)*∑ l ∈ Finset.range (m+1), theta Y l*
    ∑ u ∈ Finset.range (pivot+l-1), ∑ i ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        f i ((u : ℤ)::selected (d.map Int.ofNat) I) (g-i)
          (((pivot : ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length)\I))
lemma linearSum_smul (Y : ℝ) (g pivot : ℕ) (d : List ℕ) (f : ℕ → List ℤ → ℝ) (A : ℝ) :
    linearSum Y g pivot d (fun g' ds => A*f g' ds)=A*linearSum Y g pivot d f := by
  unfold linearSum
  dsimp only
  split_ifs
  · simp only [add_zero,mul_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  · simp only [mul_add,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      ring
    · apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro u hu
      ring
lemma separatingSum_smul (Y : ℝ) (g pivot : ℕ) (d : List ℕ)
    (f : ℕ → List ℤ → ℕ → List ℤ → ℝ) (A : ℝ) :
    separatingSum Y g pivot d (fun i ds₁ j ds₂ => A*f i ds₁ j ds₂)=A*separatingSum Y g pivot d f := by
  unfold separatingSum
  dsimp only
  simp only [Finset.mul_sum,mul_assoc]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro I hI
  ring
lemma linearSum_div (Y : ℝ) (g pivot : ℕ) (d : List ℕ) (f : ℕ → List ℤ → ℝ) (D : ℝ) :
    linearSum Y g pivot d (fun g' ds => f g' ds/D)=linearSum Y g pivot d f/D := by
  have he := linearSum_smul Y g pivot d f D⁻¹
  simpa only [div_eq_mul_inv,mul_comm] using he
lemma separatingSum_div (Y : ℝ) (g pivot : ℕ) (d : List ℕ)
    (f : ℕ → List ℤ → ℕ → List ℤ → ℝ) (D : ℝ) :
    separatingSum Y g pivot d (fun i ds₁ j ds₂ => f i ds₁ j ds₂/D)=separatingSum Y g pivot d f/D := by
  have he := separatingSum_smul Y g pivot d f D⁻¹
  simpa only [div_eq_mul_inv,mul_comm] using he
lemma linearSum_mono (Y : ℝ) (g pivot : ℕ) (d : List ℕ) (f f' : ℕ → List ℤ → ℝ)
    (hY : Y ∈ Set.Icc 0 y₀)
    (hm : ∀ j ∈ Finset.range d.length, ∀ l ∈ Finset.range (deficit g (pivot::d)+1),
      f g (((pivot : ℤ)+d[j]!+l-1)::(d.eraseIdx j).map Int.ofNat) ≤
        f' g (((pivot : ℤ)+d[j]!+l-1)::(d.eraseIdx j).map Int.ofNat))
    (hn : ∀ l ∈ Finset.range (deficit g (pivot::d)+1), ∀ u ∈ Finset.range (pivot+l-1),
      f (g-1) ((u : ℤ)::((pivot : ℤ)+l-2-u)::d.map Int.ofNat) ≤
        f' (g-1) ((u : ℤ)::((pivot : ℤ)+l-2-u)::d.map Int.ofNat)) :
    linearSum Y g pivot d f ≤ linearSum Y g pivot d f' := by
  unfold linearSum
  dsimp only
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro l hl
    exact mul_le_mul_of_nonneg_left (hm j hj l hl) (theta_nonneg Y hY l)
  · split_ifs
    · exact le_rfl
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro l hl
      apply mul_le_mul_of_nonneg_left _ (theta_nonneg Y hY l)
      exact Finset.sum_le_sum (fun u hu => hn l hl u hu)
lemma separatingSum_mono (Y : ℝ) (g pivot : ℕ) (d : List ℕ)
    (f f' : ℕ → List ℤ → ℕ → List ℤ → ℝ) (hY : Y ∈ Set.Icc 0 y₀)
    (hs : ∀ l ∈ Finset.range (deficit g (pivot::d)+1), ∀ u ∈ Finset.range (pivot+l-1),
      ∀ i ∈ Finset.range (g+1), ∀ I ∈ (Finset.range d.length).powerset,
      f i ((u : ℤ)::selected (d.map Int.ofNat) I) (g-i)
        (((pivot : ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length)\I)) ≤
      f' i ((u : ℤ)::selected (d.map Int.ofNat) I) (g-i)
        (((pivot : ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length)\I))) :
    separatingSum Y g pivot d f ≤ separatingSum Y g pivot d f' := by
  unfold separatingSum
  dsimp only
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro l hl
  apply mul_le_mul_of_nonneg_left _ (theta_nonneg Y hY l)
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.sum_le_sum (fun I hI => hs l hl u hu i hi I hI)
lemma positiveRHS_eq_sums (P : PsiTheory) (Y : ℝ) (g pivot : ℕ) (d : List ℕ) :
    positiveRHS P g pivot d Y =
      linearSum Y g pivot d (fun g' ds => normInt P g' ds Y)+
      separatingSum Y g pivot d (fun i ds₁ j ds₂ => normInt P i ds₁ Y*normInt P j ds₂ Y) := rfl
lemma weightedLinear_eq_sum (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) :
    weightedLinear c Y g pivot d = linearSum Y g pivot d
      (fun g' ds => validModel g' ds Y/model g (pivot::d) Y*signedWeight c ds/clippedWeight c (pivot::d)) := rfl
lemma weightedSeparating_eq_sum (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) :
    weightedSeparating c Y g pivot d = separatingSum Y g pivot d
      (fun i ds₁ j ds₂ => validModel i ds₁ Y*validModel j ds₂ Y/model g (pivot::d) Y*
        signedWeight c ds₁*signedWeight c ds₂/clippedWeight c (pivot::d)*
          Real.exp ((1/12 : ℝ)*min (complexity i ds₁.length) (complexity j ds₂.length))) := rfl
theorem weighted_recursion_upper (P : PsiTheory) (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (L S : ℝ)
    (hg : 2 ≤ g) (hd : (pivot::d).sum ≤ dimension g (d.length+1)) (hY : Y ∈ Set.Icc 0 y₀)
    (hmerge : ∀ j ∈ Finset.range d.length, ∀ l ∈ Finset.range (deficit g (pivot::d)+1),
      let ds := ((pivot : ℤ)+d[j]!+l-1)::(d.eraseIdx j).map Int.ofNat
      validModel g ds Y ≠ 0 → ratio P g (ds.map Int.toNat) Y/signedWeight c ds ≤ L)
    (hcontract : ∀ l ∈ Finset.range (deficit g (pivot::d)+1), ∀ u ∈ Finset.range (pivot+l-1),
      let ds := (u : ℤ)::((pivot : ℤ)+l-2-u)::d.map Int.ofNat
      validModel (g-1) ds Y ≠ 0 → ratio P (g-1) (ds.map Int.toNat) Y/signedWeight c ds ≤ L)
    (hseparate : ∀ l ∈ Finset.range (deficit g (pivot::d)+1), ∀ u ∈ Finset.range (pivot+l-1),
      ∀ i ∈ Finset.range (g+1), ∀ I ∈ (Finset.range d.length).powerset,
      let ds₁ := (u : ℤ)::selected (d.map Int.ofNat) I
      let ds₂ := ((pivot : ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length)\I)
      validModel i ds₁ Y ≠ 0 → validModel (g-i) ds₂ Y ≠ 0 →
      (ratio P i (ds₁.map Int.toNat) Y/signedWeight c ds₁)*
        (ratio P (g-i) (ds₂.map Int.toNat) Y/signedWeight c ds₂) ≤
        S*Real.exp ((1/12 : ℝ)*min (complexity i ds₁.length) (complexity (g-i) ds₂.length))) :
    ratio P g (pivot::d) Y/clippedWeight c (pivot::d) ≤
      L*weightedLinear c Y g pivot d+S*weightedSeparating c Y g pivot d := by
  let M := model g (pivot::d) Y
  let W := clippedWeight c (pivot::d)
  let D := M*W
  have hM : 0 < M := model_pos g _ Y (by unfold Stable; simp only [List.length_cons]; omega) hY
  have hW : 0 < W := clippedWeight_pos c _
  have hD : 0 < D := mul_pos hM hW
  have hlinear (g' : ℕ) (ds : List ℤ)
      (hcap : validModel g' ds Y ≠ 0 → ratio P g' (ds.map Int.toNat) Y/signedWeight c ds ≤ L) :
      normInt P g' ds Y/D ≤
        L*(validModel g' ds Y/model g (pivot::d) Y*signedWeight c ds/clippedWeight c (pivot::d)) := by
    have he := div_le_div_of_nonneg_right (normInt_weighted_upper P c Y g' ds L hY hcap) hD.le
    convert he using 1 <;> dsimp only [D,M,W] <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
  have hsep (i j : ℕ) (ds₁ ds₂ : List ℤ)
      (hcap : validModel i ds₁ Y ≠ 0 → validModel j ds₂ Y ≠ 0 →
        (ratio P i (ds₁.map Int.toNat) Y/signedWeight c ds₁)*
          (ratio P j (ds₂.map Int.toNat) Y/signedWeight c ds₂) ≤
          S*Real.exp ((1/12 : ℝ)*min (complexity i ds₁.length) (complexity j ds₂.length))) :
      (normInt P i ds₁ Y*normInt P j ds₂ Y)/D ≤
        S*(validModel i ds₁ Y*validModel j ds₂ Y/model g (pivot::d) Y*
          signedWeight c ds₁*signedWeight c ds₂/clippedWeight c (pivot::d)*
            Real.exp ((1/12 : ℝ)*min (complexity i ds₁.length) (complexity j ds₂.length))) := by
    have he := div_le_div_of_nonneg_right (normInt_product_weighted_upper P c Y i j ds₁ ds₂
      (S*Real.exp ((1/12 : ℝ)*min (complexity i ds₁.length) (complexity j ds₂.length))) hY hcap) hD.le
    convert he using 1 <;> dsimp only [D,M,W] <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
  have hrec : ratio P g (pivot::d) Y/clippedWeight c (pivot::d) =
      linearSum Y g pivot d (fun g' ds => normInt P g' ds Y/D)+
      separatingSum Y g pivot d (fun i ds₁ j ds₂ => normInt P i ds₁ Y*normInt P j ds₂ Y/D) := by
    unfold ratio
    rw [div_div,positive_recursion P g pivot d Y (by unfold complexity; omega) hd hY,
      positiveRHS_eq_sums,add_div,← linearSum_div,← separatingSum_div]
  calc
    _ = _ := hrec
    _ ≤ linearSum Y g pivot d
        (fun g' ds => L*(validModel g' ds Y/model g (pivot::d) Y*signedWeight c ds/clippedWeight c (pivot::d)))+
        separatingSum Y g pivot d
        (fun i ds₁ j ds₂ => S*(validModel i ds₁ Y*validModel j ds₂ Y/model g (pivot::d) Y*
          signedWeight c ds₁*signedWeight c ds₂/clippedWeight c (pivot::d)*
            Real.exp ((1/12 : ℝ)*min (complexity i ds₁.length) (complexity j ds₂.length)))) := by
      apply add_le_add
      · apply linearSum_mono _ _ _ _ _ _ hY
        · intro j hj l hl
          exact hlinear _ _ (hmerge j hj l hl)
        · intro l hl u hu
          exact hlinear _ _ (hcontract l hl u hu)
      · apply separatingSum_mono _ _ _ _ _ _ hY
        intro l hl u hu i hi I hI
        exact hsep _ _ _ _ (hseparate l hl u hu i hi I hI)
    _ = _ := by
      rw [linearSum_smul,separatingSum_smul,← weightedLinear_eq_sum,← weightedSeparating_eq_sum]
lemma validModel_ne_zero_support (g : ℕ) (ds : List ℤ) (Y : ℝ) (hv : validModel g ds Y ≠ 0) :
    (∀ k ∈ ds, 0 ≤ k) ∧ Stable g ds.length ∧ (ds.map Int.toNat).sum ≤ dimension g ds.length := by
  by_contra h
  unfold validModel at hv
  rw [if_neg h] at hv
  exact hv rfl
lemma clippedRatio_nonneg_of_validModel (P : PsiTheory) (c Y : ℝ) (g : ℕ) (ds : List ℤ)
    (hY : Y ∈ Set.Icc 0 y₀) (hn : 1 ≤ ds.length) (hv : validModel g ds Y ≠ 0) :
    0 ≤ ratio P g (ds.map Int.toNat) Y/signedWeight c ds := by
  have hV : 0 < validModel g ds Y := lt_of_le_of_ne (validModel_nonneg g ds Y hY) (Ne.symm hv)
  have hnorm := normInt_nonneg_nonempty P g ds hn Y hY
  rw [normInt_eq_validModel_mul_ratio P g ds Y hY] at hnorm
  have hr : 0 ≤ ratio P g (ds.map Int.toNat) Y := by nlinarith
  exact div_nonneg hr (signedWeight_pos c ds).le
end WP.Comparison
