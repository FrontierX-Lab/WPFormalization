import WPFormalization.HigherOrder.MajorantFinite

/-! The lexicographic dependency and comparison argument of Lemma C.2.
Every coefficient on row i at degree j depends only on earlier (degree,row)
pairs. This yields formal uniqueness, nonnegativity, and ENNReal comparison
without any assumption that the proposed extended coefficients are finite.
-/
noncomputable section
namespace WP.Majorant
open scoped ENNReal
variable {R : Type*} [CommSemiring R]

lemma substitutionCoeff_zero {m : ℕ} (Φ : MvPowerSeries (Option (Fin m)) R)
    (E : Fin m → PowerSeries R) : substitutionCoeff Φ E 0 = MvPowerSeries.coeff 0 Φ := by
  have hα : ∀ α : Option (Fin m) → Fin 1, α = fun _ => 0 := by
    intro α
    funext s
    exact Subsingleton.elim _ _
  have hz : Finsupp.equivFunOnFinite.symm (fun _ : Option (Fin m) => (0:ℕ)) = 0 := by ext s; rfl
  unfold substitutionCoeff
  rw [Finset.sum_eq_single (fun _ => 0)]
  · simp [hz]
  · intro α hαmem hαne
    exact (hαne (hα α)).elim
  · simp

def argumentSeries {m : ℕ} (E : Fin m → PowerSeries R) : Option (Fin m) → PowerSeries R
  | none => PowerSeries.X
  | some i => E i

def earlier {m : ℕ} (j : ℕ) (i : Fin m) (k : ℕ) (l : Fin m) : Prop :=
  k < j ∨ k = j ∧ l.val < i.val

instance earlierDecidable {m : ℕ} (j : ℕ) (i : Fin m) (k : ℕ) (l : Fin m) :
    Decidable (earlier j i k l) := inferInstanceAs (Decidable (k < j ∨ k = j ∧ l.val < i.val))

def cut {m : ℕ} (j : ℕ) (i : Fin m) (E : Fin m → PowerSeries R) (l : Fin m) : PowerSeries R :=
  PowerSeries.mk (fun k => if earlier j i k l then PowerSeries.coeff k (E l) else 0)

lemma cut_zero {m : ℕ} (j : ℕ) (i : Fin m) (E : Fin m → PowerSeries R)
    (hE : ∀ l, PowerSeries.coeff 0 (E l) = 0) :
    ∀ l, PowerSeries.coeff 0 (cut j i E l) = 0 := by
  intro l
  simp [cut,hE]

lemma cut_agree {m : ℕ} (j : ℕ) (i : Fin m) (E : Fin m → PowerSeries R) :
    ∀ s, AgreeBelow j (argumentSeries E s) (argumentSeries (cut j i E) s) := by
  intro s k hk
  cases s with
  | none => rfl
  | some l => simp [argumentSeries,cut,earlier,hk]

lemma argumentSeries_zero {m : ℕ} (E : Fin m → PowerSeries R)
    (hE : ∀ l, PowerSeries.coeff 0 (E l) = 0) :
    ∀ s, PowerSeries.coeff 0 (argumentSeries E s) = 0 := by
  intro s
  cases s <;> simp [argumentSeries,hE]

lemma factor_argumentSeries_prod {m : ℕ} (α : Option (Fin m) →₀ ℕ) (E : Fin m → PowerSeries R) :
    ((factors α).map (argumentSeries E)).prod = PowerSeries.X^(α none)*∏ l, E l^(α (some l)) := by
  rw [factors_prod_fintype,Fintype.prod_option]
  rfl

lemma monomial_cut {m : ℕ} (j : ℕ) (hj : 1 ≤ j) (i : Fin m)
    (Φ : MvPowerSeries (Option (Fin m)) R) (E : Fin m → PowerSeries R)
    (hE : ∀ l, PowerSeries.coeff 0 (E l) = 0)
    (htri : ∀ l : Fin m, i.val ≤ l.val → MvPowerSeries.coeff (Finsupp.single (some l) 1) Φ = 0)
    (α : Option (Fin m) →₀ ℕ) :
    MvPowerSeries.coeff α Φ * PowerSeries.coeff j ((factors α).map (argumentSeries E)).prod =
      MvPowerSeries.coeff α Φ * PowerSeries.coeff j ((factors α).map (argumentSeries (cut j i E))).prod := by
  by_cases hlen₀ : (factors α).length = 0
  · have hl : factors α = [] := by simpa using hlen₀
    simp [hl]
  · by_cases hlen₁ : (factors α).length = 1
    · have hsum : α.sum (fun _ n => n) = 1 := by rwa [← factors_length]
      obtain ⟨s,hs⟩ := (Finsupp.sum_eq_one_iff α).1 hsum
      rw [hs,factors_single]
      simp only [List.map_singleton,List.prod_singleton]
      cases s with
      | none => rfl
      | some l =>
          by_cases hli : l.val < i.val
          · simp [argumentSeries,cut,earlier,hli]
          · rw [htri l (by omega),zero_mul,zero_mul]
    · congr 1
      apply listprod_coeff_congr_of_two (factors α) (argumentSeries E) (argumentSeries (cut j i E)) j
        (by omega) (argumentSeries_zero E hE) (argumentSeries_zero _ (cut_zero j i E hE)) (cut_agree j i E)

lemma substitutionCoeff_cut {m : ℕ} (j : ℕ) (hj : 1 ≤ j) (i : Fin m)
    (Φ : MvPowerSeries (Option (Fin m)) R) (E : Fin m → PowerSeries R)
    (hE : ∀ l, PowerSeries.coeff 0 (E l) = 0)
    (htri : ∀ l : Fin m, i.val ≤ l.val → MvPowerSeries.coeff (Finsupp.single (some l) 1) Φ = 0) :
    substitutionCoeff Φ E j = substitutionCoeff Φ (cut j i E) j := by
  unfold substitutionCoeff
  apply Finset.sum_congr rfl
  intro α hα
  split_ifs with hdegree
  · let a : Option (Fin m) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun s => (α s).val)
    have heE : PowerSeries.X^((α none).val)*∏ l, E l^((α (some l)).val) =
        ((factors a).map (argumentSeries E)).prod := by rw [factor_argumentSeries_prod]; rfl
    have heF : PowerSeries.X^((α none).val)*∏ l, cut j i E l^((α (some l)).val) =
        ((factors a).map (argumentSeries (cut j i E))).prod := by rw [factor_argumentSeries_prod]; rfl
    rw [heE,heF]
    exact monomial_cut j hj i Φ E hE htri a
  · rfl

lemma substitutionCoeff_mono {m : ℕ} (Φ : MvPowerSeries (Option (Fin m)) ℝ≥0∞)
    (E F : Fin m → PowerSeries ℝ≥0∞) (j : ℕ)
    (h : ∀ l, LeBelow (j+1) (E l) (F l)) :
    substitutionCoeff Φ E j ≤ substitutionCoeff Φ F j := by
  unfold substitutionCoeff
  apply Finset.sum_le_sum
  intro α hα
  split_ifs with hdegree
  · let a : Option (Fin m) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun s => (α s).val)
    have heE : PowerSeries.X^((α none).val)*∏ l, E l^((α (some l)).val) =
        ((factors a).map (argumentSeries E)).prod := by rw [factor_argumentSeries_prod]; rfl
    have heF : PowerSeries.X^((α none).val)*∏ l, F l^((α (some l)).val) =
        ((factors a).map (argumentSeries F)).prod := by rw [factor_argumentSeries_prod]; rfl
    rw [heE,heF]
    apply mul_le_mul' le_rfl
    apply leBelow_listprod (n := j+1) (factors a) (argumentSeries E) (argumentSeries F) ?_ j (by omega)
    intro s k hk
    cases s with
    | none => exact le_rfl
    | some l => exact h l k hk
  · exact le_rfl

lemma substitutionCoeff_mono_earlier {m : ℕ} (j : ℕ) (hj : 1 ≤ j) (i : Fin m)
    (Φ : MvPowerSeries (Option (Fin m)) ℝ≥0∞) (E F : Fin m → PowerSeries ℝ≥0∞)
    (hE : ∀ l, PowerSeries.coeff 0 (E l) = 0) (hF : ∀ l, PowerSeries.coeff 0 (F l) = 0)
    (htri : ∀ l : Fin m, i.val ≤ l.val → MvPowerSeries.coeff (Finsupp.single (some l) 1) Φ = 0)
    (h : ∀ l k, earlier j i k l → PowerSeries.coeff k (E l) ≤ PowerSeries.coeff k (F l)) :
    substitutionCoeff Φ E j ≤ substitutionCoeff Φ F j := by
  rw [substitutionCoeff_cut j hj i Φ E hE htri,substitutionCoeff_cut j hj i Φ F hF htri]
  apply substitutionCoeff_mono
  intro l k hk
  simp only [cut,PowerSeries.coeff_mk]
  split_ifs with he
  · exact h l k he
  · exact le_rfl

lemma substitutionCoeff_congr_earlier {m : ℕ} (j : ℕ) (hj : 1 ≤ j) (i : Fin m)
    (Φ : MvPowerSeries (Option (Fin m)) R) (E F : Fin m → PowerSeries R)
    (hE : ∀ l, PowerSeries.coeff 0 (E l) = 0) (hF : ∀ l, PowerSeries.coeff 0 (F l) = 0)
    (htri : ∀ l : Fin m, i.val ≤ l.val → MvPowerSeries.coeff (Finsupp.single (some l) 1) Φ = 0)
    (h : ∀ l k, earlier j i k l → PowerSeries.coeff k (E l) = PowerSeries.coeff k (F l)) :
    substitutionCoeff Φ E j = substitutionCoeff Φ F j := by
  rw [substitutionCoeff_cut j hj i Φ E hE htri,substitutionCoeff_cut j hj i Φ F hF htri]
  congr 1
  funext l
  ext k
  simp only [cut,PowerSeries.coeff_mk]
  split_ifs with he
  · exact h l k he
  · rfl

lemma fixedPoint_unique {m : ℕ} (Φ : Fin m → MvPowerSeries (Option (Fin m)) R)
    (htri : ∀ i l : Fin m, i.val ≤ l.val → MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i) = 0)
    (U V : Fin m → PowerSeries R)
    (hU₀ : ∀ i, PowerSeries.coeff 0 (U i) = 0) (hV₀ : ∀ i, PowerSeries.coeff 0 (V i) = 0)
    (hU : ∀ i j, PowerSeries.coeff j (U i) = substitutionCoeff (Φ i) U j)
    (hV : ∀ i j, PowerSeries.coeff j (V i) = substitutionCoeff (Φ i) V j) : U = V := by
  have hmain : ∀ j i, PowerSeries.coeff j (U i) = PowerSeries.coeff j (V i) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j hj =>
      intro i
      refine Fin.strong_induction_on (fun i hi => ?_) i
      by_cases hj₀ : j = 0
      · subst j
        rw [hU₀,hV₀]
      · rw [hU i j,hV i j]
        apply substitutionCoeff_congr_earlier j (by omega) i (Φ i) U V hU₀ hV₀ (htri i)
        intro l k he
        rcases he with hk | ⟨rfl,hl⟩
        · exact hj k hk l
        · exact hi l hl
  funext i
  ext j
  exact hmain j i

lemma extended_subsolution_le_fixedPoint {m : ℕ}
    (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ≥0∞)
    (htri : ∀ i l : Fin m, i.val ≤ l.val → MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i) = 0)
    (U : Fin m → PowerSeries ℝ≥0∞)
    (hU₀ : ∀ i, PowerSeries.coeff 0 (U i) = 0)
    (hU : ∀ i j, PowerSeries.coeff j (U i) = substitutionCoeff (Φ i) U j)
    (e : Fin m → ℕ → ℝ≥0∞) (he₀ : ∀ i, e i 0 = 0)
    (he : ∀ i j, 1 ≤ j → e i j ≤ substitutionCoeff (Φ i) (fun l => PowerSeries.mk (e l)) j) :
    ∀ j i, e i j ≤ PowerSeries.coeff j (U i) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j hj =>
    intro i
    refine Fin.strong_induction_on (fun i hi => ?_) i
    by_cases hj₀ : j = 0
    · subst j
      rw [he₀,hU₀]
    · calc
        e i j ≤ substitutionCoeff (Φ i) (fun l => PowerSeries.mk (e l)) j := he i j (by omega)
        _ ≤ substitutionCoeff (Φ i) U j := by
          apply substitutionCoeff_mono_earlier j (by omega) i (Φ i) _ U
            (fun l => by simpa using he₀ l) hU₀ (htri i)
          intro l k hearly
          rcases hearly with hk | ⟨rfl,hl⟩
          · simpa using hj k hk l
          · simpa using hi l hl
        _ = PowerSeries.coeff j (U i) := (hU i j).symm

lemma coeff_mul_nonneg (f g : PowerSeries ℝ)
    (hf : ∀ k, 0 ≤ PowerSeries.coeff k f) (hg : ∀ k, 0 ≤ PowerSeries.coeff k g) :
    ∀ j, 0 ≤ PowerSeries.coeff j (f*g) := by
  intro j
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg (fun p hp => mul_nonneg (hf p.1) (hg p.2))

lemma coeff_listprod_nonneg {σ : Type*} (l : List σ) (f : σ → PowerSeries ℝ)
    (hf : ∀ s k, 0 ≤ PowerSeries.coeff k (f s)) :
    ∀ j, 0 ≤ PowerSeries.coeff j (l.map f).prod := by
  induction l with
  | nil =>
      intro j
      simp only [List.map_nil,List.prod_nil,PowerSeries.coeff_one]
      split_ifs <;> norm_num
  | cons a l ih =>
      simp only [List.map_cons,List.prod_cons]
      exact coeff_mul_nonneg _ _ (hf a) ih

lemma substitutionCoeff_nonneg {m : ℕ} (Φ : MvPowerSeries (Option (Fin m)) ℝ)
    (hΦ : ∀ α, 0 ≤ MvPowerSeries.coeff α Φ) (E : Fin m → PowerSeries ℝ)
    (hE : ∀ l k, 0 ≤ PowerSeries.coeff k (E l)) (j : ℕ) :
    0 ≤ substitutionCoeff Φ E j := by
  unfold substitutionCoeff
  apply Finset.sum_nonneg
  intro α hα
  split_ifs with hdegree
  · apply mul_nonneg (hΦ _)
    let a : Option (Fin m) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun s => (α s).val)
    have heE : PowerSeries.X^((α none).val)*∏ l, E l^((α (some l)).val) =
        ((factors a).map (argumentSeries E)).prod := by rw [factor_argumentSeries_prod]; rfl
    rw [heE]
    apply coeff_listprod_nonneg
    intro s k
    cases s with
    | none => simp only [argumentSeries,PowerSeries.coeff_X]; split_ifs <;> norm_num
    | some l => exact hE l k
  · exact le_rfl

lemma fixedPoint_nonnegative {m : ℕ} (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ)
    (hΦ : ∀ i α, 0 ≤ MvPowerSeries.coeff α (Φ i))
    (htri : ∀ i l : Fin m, i.val ≤ l.val → MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i) = 0)
    (U : Fin m → PowerSeries ℝ) (hU₀ : zeroConstant U) (hU : formalFixedPoint Φ U) :
    ∀ j i, 0 ≤ PowerSeries.coeff j (U i) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j hj =>
    intro i
    refine Fin.strong_induction_on (fun i hi => ?_) i
    by_cases hj₀ : j = 0
    · subst j
      rw [hU₀ i]
    · rw [hU i j,substitutionCoeff_cut j (by omega) i (Φ i) U hU₀ (htri i)]
      apply substitutionCoeff_nonneg _ (hΦ i)
      intro l k
      simp only [cut,PowerSeries.coeff_mk]
      split_ifs with he
      · rcases he with hk | ⟨rfl,hl⟩
        · exact hj k hk l
        · exact hi l hl
      · exact le_rfl

end WP.Majorant
