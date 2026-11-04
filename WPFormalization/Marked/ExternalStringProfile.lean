import WPFormalization.Marked.ExternalStringBoundary
import WPFormalization.Marked.SingleMarkingProfile
noncomputable section
namespace WP
open Set
lemma shifted_unweighted_ratio_eq_profile (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hp : 1 ≤ d.length) (hs : Stable g d.length) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    (shifted P g d Y / externalOddWeight d) / shifted P g (List.replicate d.length 0) Y =
      r Y ^ d.sum * profile P g d Y / externalOddWeight d := by
  by_cases hd : d.sum ≤ dimension g d.length
  · have ha := (a_pos Y hY).ne'
    have hr := (r_pos Y hY).ne'
    have hz : shifted P g (List.replicate d.length 0) Y ≠ 0 := by
      have hn := normalized_pos_valid_nonempty P g (List.replicate d.length 0)
        (by simpa using hp) (by simpa using hs) (by simp) Y ⟨hY.1,hY.2.le⟩
      rw [normalized,ite_eq_right (ne_of_lt hY.2)] at hn
      exact (mul_pos_iff_of_pos_left (mul_pos (pow_pos (a_pos Y hY) _) (pow_pos (r_pos Y hY) _))).mp hn |>.ne'
    have hm : dimension g d.length = deficit g d + d.sum := by unfold deficit;omega
    unfold profile normalized
    simp only [ite_eq_right (ne_of_lt hY.2),List.length_replicate,deficit,List.sum_replicate,nsmul_zero,Nat.sub_zero]
    rw [hm,pow_add]
    simp only [Nat.add_sub_cancel]
    field_simp
    <;>ring
  · have hz : shifted P g d Y = 0 := by simp [shifted,hd]
    simp [profile,normalized,ite_eq_right (ne_of_lt hY.2),hz]
end WP
namespace WP.BoundaryConvolution
open Set
lemma stringBoundaryAmplitude_ratio (P : PsiTheory) (g : ℕ) {p : ℕ} (hp : 1 ≤ p)
    (hs : Stable g p) (t : Fin p → ℝ) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    stringBoundaryAmplitude P g t 0 Y / shifted P g (List.replicate p 0) Y =
      ∑ b ∈ externalDegreeBox p (dimension g p),
        profile P g (List.ofFn b) Y *
          ∏ i, (r Y ^ b i / (oddFactorial (b i):ℝ) * realTranslationWeight (t i) (b i) Y) := by
  unfold stringBoundaryAmplitude externalStringAmplitude
  simp only [zero_add,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  have he := shifted_unweighted_ratio_eq_profile P g (List.ofFn b)
    (by simpa using hp) (by simpa using hs) Y hY
  simp only [List.length_ofFn,externalMarkedAmplitude,List.replicate_zero,List.nil_append] at *
  rw [mul_div_right_comm,he]
  simp only [externalOddWeight,List.map_ofFn,List.prod_ofFn,List.sum_ofFn,
    Finset.prod_mul_distrib,Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum,Function.comp_def]
  ring
end WP.BoundaryConvolution
namespace WP.BoundaryConvolution
open Set
/-- The literal b-weight of Eq.9.26, after summing its entire a-series. -/
def boundaryProfileWeight {p : ℕ} (t : Fin p → ℝ) (Y : ℝ) (b : Fin p → ℕ) : ℝ :=
  ∏ i, r Y ^ b i / (oddFactorial (b i):ℝ) * realTranslationWeight (t i) (b i) Y

def boundaryProfileMoment {p : ℕ} (b : Fin p → ℕ) : ℝ :=
  ((∑ i, b i : ℕ):ℝ) * (((∑ i, b i : ℕ):ℝ)+1)

lemma boundaryProfileWeight_nonneg {p : ℕ} (t : Fin p → ℝ) (ht : ∀ i, 0 ≤ t i)
    (Y : ℝ) (hY : Y ∈ Ico 0 y₀) (b : Fin p → ℕ) : 0 ≤ boundaryProfileWeight t Y b := by
  apply Finset.prod_nonneg
  intro i hi
  exact mul_nonneg (div_nonneg (pow_nonneg (r_pos Y hY).le _) (Nat.cast_nonneg _))
    (realTranslationWeight_nonneg (t i) (ht i) (b i) Y hY.1)

lemma stringBoundaryAmplitude_ratio_hasSum (P : PsiTheory) (g : ℕ) {p : ℕ} (hp : 1 ≤ p)
    (hs : Stable g p) (t : Fin p → ℝ) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    HasSum (fun b : Fin p → ℕ => profile P g (List.ofFn b) Y * boundaryProfileWeight t Y b)
      (stringBoundaryAmplitude P g t 0 Y / shifted P g (List.replicate p 0) Y) := by
  rw [stringBoundaryAmplitude_ratio P g hp hs t Y hY]
  apply hasSum_sum_of_ne_finset_zero
  intro b hb
  have he : ∃ i, dimension g p < b i := by
    rw [mem_externalDegreeBox] at hb
    push Not at hb
    exact hb
  obtain ⟨i,hi⟩ := he
  have hsingle : b i ≤ ∑ j, b j := Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ i)
  rw [profile_excess_zero P g (List.ofFn b) Y (by simpa only [List.length_ofFn,List.sum_ofFn] using hi.trans_le hsingle),zero_mul]

lemma stringBoundaryAmplitude_ratio_tsum (P : PsiTheory) (g : ℕ) {p : ℕ} (hp : 1 ≤ p)
    (hs : Stable g p) (t : Fin p → ℝ) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    stringBoundaryAmplitude P g t 0 Y / shifted P g (List.replicate p 0) Y =
      ∑' b : Fin p → ℕ, profile P g (List.ofFn b) Y * boundaryProfileWeight t Y b :=
  (stringBoundaryAmplitude_ratio_hasSum P g hp hs t Y hY).tsum_eq.symm

lemma stringBoundaryAmplitude_profile_error (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ t : Fin p → ℝ, (∀ i, 0 ≤ t i) →
    ∀ Y ∈ Ico 0 y₀, ∀ B M : ℝ,
    HasSum (boundaryProfileWeight t Y) B →
    HasSum (fun b => boundaryProfileMoment b * boundaryProfileWeight t Y b) M →
    0 ≤ B - stringBoundaryAmplitude P g t 0 Y / shifted P g (List.replicate p 0) Y ∧
      B - stringBoundaryAmplitude P g t 0 Y / shifted P g (List.replicate p 0) Y ≤ C*M/g := by
  obtain ⟨C,hC,hquad⟩ := quadratic_profile_all_markings_proof P p hp
  refine ⟨C,hC,?_⟩
  intro g hg t ht Y hY B M hB hM
  have hs : Stable g p := by unfold Stable;omega
  have hactual := stringBoundaryAmplitude_ratio_hasSum P g hp hs t Y hY
  have herr := hB.sub hactual
  have hnonneg : ∀ b : Fin p → ℕ,
      0 ≤ boundaryProfileWeight t Y b - profile P g (List.ofFn b) Y * boundaryProfileWeight t Y b := by
    intro b
    have hq := (hquad g hg (List.ofFn b) (by simp) Y ⟨hY.1,hY.2.le⟩).1
    nlinarith [mul_nonneg hq (boundaryProfileWeight_nonneg t ht Y hY b)]
  refine ⟨herr.nonneg hnonneg,?_⟩
  have hupper : ∀ b : Fin p → ℕ,
      boundaryProfileWeight t Y b - profile P g (List.ofFn b) Y * boundaryProfileWeight t Y b ≤
        (C/(g:ℝ)) * (boundaryProfileMoment b * boundaryProfileWeight t Y b) := by
    intro b
    have hq := (hquad g hg (List.ofFn b) (by simp) Y ⟨hY.1,hY.2.le⟩).2
    have hm := mul_le_mul_of_nonneg_right hq (boundaryProfileWeight_nonneg t ht Y hY b)
    simp only [List.sum_ofFn] at hm
    dsimp only [boundaryProfileMoment]
    convert hm using 1 <;> ring
  have hu := hasSum_le hupper herr (hM.mul_left (C/(g:ℝ)))
  convert hu using 1 <;> ring
end WP.BoundaryConvolution
namespace WP.BoundaryConvolution
open Set
lemma stringBoundaryAmplitude_profile_relative_error (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ t : Fin p → ℝ, (∀ i, 0 ≤ t i) →
    ∀ Y ∈ Ico 0 y₀, ∀ B M : ℝ, 1 ≤ B →
    HasSum (boundaryProfileWeight t Y) B →
    HasSum (fun b => boundaryProfileMoment b * boundaryProfileWeight t Y b) M →
    |stringBoundaryAmplitude P g t 0 Y / (shifted P g (List.replicate p 0) Y * B) - 1| ≤ C*M/g := by
  obtain ⟨C,hC,herr⟩ := stringBoundaryAmplitude_profile_error P p hp
  refine ⟨C,hC,?_⟩
  intro g hg t ht Y hY B M hB hs hM
  have he := herr g hg t ht Y hY B M hs hM
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hid : stringBoundaryAmplitude P g t 0 Y / (shifted P g (List.replicate p 0) Y * B) - 1 =
      -(B - stringBoundaryAmplitude P g t 0 Y / shifted P g (List.replicate p 0) Y) / B := by
    field_simp
    <;>ring
  rw [hid,abs_div,abs_neg,abs_of_nonneg he.1,abs_of_pos hB0]
  exact (div_le_self he.1 hB).trans he.2
end WP.BoundaryConvolution
