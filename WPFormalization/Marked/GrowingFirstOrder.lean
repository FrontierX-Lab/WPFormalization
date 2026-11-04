import WPFormalization.Marked.GrowingCusp
import WPFormalization.Marked.GenusExtensions
import WPFormalization.Marked.GenusRatio

/-! Lemma C.6 in its original complete scope: growing positive marking counts, every degree tuple, and both original normalized scalar errors, uniformly on the closed physical interval. -/
noncomputable section
namespace WP
open Set
lemma growing_marking_genus_first_order_proof (P : PsiTheory) (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ,0 < C ∧ ∃ H : ℕ,∀g p:ℕ,1 ≤ p → H ≤ complexity g p →
      (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) → ∀Y∈Icc (0:ℝ) y₀,
      |genusCorrection P g p Y-1| ≤ C*((p:ℝ)+1)/(complexity g p:ℝ) := by
  obtain ⟨Cp,hCp,Hp,hprofile⟩ := growing_marking_profile_first_order_proof P M hM
  obtain ⟨Ct,hCt,Ht,hS,hT⟩ := separating_growing_markings_bounds P M hM
  obtain ⟨Co,hCo,Go,hO⟩ := marked_genus_all_proof P 1
  obtain ⟨J,hJ⟩ := exists_nat_ge (4*M^2+1)
  let C : ℝ := 2*Cp+2*Ct+2*Co+1
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨C,hC,Hp+Ht+2*(Go+2)+J+8,?_⟩
  intro g p hp hH hpM Y hY
  have hh8 : (8:ℝ) ≤ complexity g p := by exact_mod_cast (show 8 ≤ complexity g p by omega)
  have hh : (0:ℝ) < complexity g p := by linarith
  have hhM : 4*M^2+1 ≤ (complexity g p:ℝ) := hJ.trans (by exact_mod_cast (show J ≤ complexity g p by omega))
  have hs : Stable g p := by unfold Stable complexity at *;omega
  have hcomp := complexity_le_four_genus_growing g p hs M hM hpM hhM
  have hg2 : 2 ≤ g := by exact_mod_cast (show (2:ℝ) ≤ g by linarith only [hh8,hcomp])
  have hg : (0:ℝ) < g := by exact_mod_cast (show 0<g by omega)
  by_cases hp1 : p=1
  · rcases hp1 with rfl
    have hgGo : Go ≤ g := by unfold complexity at hH;omega
    have he := hO g hgGo Y hY
    have he' : |genusCorrection P g 1 Y-1| ≤ Co/(g:ℝ) := by
      rw [genusCorrection_of_pos P g 1 Y (by omega)]
      exact he
    apply he'.trans
    simp only [Nat.cast_one]
    apply (div_le_div_iff₀ hg hh).mpr
    have hf := mul_le_mul_of_nonneg_left hcomp hCo.le
    have hCcoef : 4*Co ≤ 2*C := by dsimp [C];linarith
    have hj := mul_le_mul_of_nonneg_right hCcoef hg.le
    nlinarith only [hf,hj]
  · have hp2 : 2 ≤ p := by omega
    let d : List ℕ := 1::List.replicate (p-1) 0
    have hd : d.length=p := by dsimp [d];simp;omega
    have hq := hprofile g p hp (by omega) hpM Y hY d hd
    have hb := hq.2.trans (min_le_right 1 _)
    simp only [d,List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,Nat.cast_one,mul_one] at hb
    have ht := hT g p hp2 (by omega) hpM Y hY
    have ht0 : 0 ≤ separatingT P g p Y := by
      rw [separatingT_eq_markedSplitConvolution P g p hp2 Y]
      exact markedSplitConvolution_nonneg P g p 2 hg2 hp2 (Or.inr rfl) Y hY
    have hk := normalized_kdv_profile P g p (by omega) hp2 Y hY
    have hid : genusCorrection P g p Y-1=(profile P g d Y-1)-(3/2:ℝ)*separatingT P g p Y := by
      rw [genusCorrection_of_pos P g p Y (by omega)]
      change profile P g d Y=_ at hk
      linarith only [hk]
    rw [hid]
    have herr : |profile P g d Y-1|=1-profile P g d Y := by rw [abs_sub_comm,abs_of_nonneg hq.1]
    calc
      _ ≤ |profile P g d Y-1|+|(3/2:ℝ)*separatingT P g p Y| := abs_sub _ _
      _ = (1-profile P g d Y)+(3/2:ℝ)*separatingT P g p Y := by rw [herr,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2),abs_of_nonneg ht0]
      _ ≤ Cp*(1+(p:ℝ)+1)/(complexity g p:ℝ)+(3/2:ℝ)*(Ct*((p:ℝ)+1)/(complexity g p:ℝ)) :=
        add_le_add hb (mul_le_mul_of_nonneg_left ht (by norm_num))
      _ = (Cp*(1+(p:ℝ)+1)+(3/2:ℝ)*Ct*((p:ℝ)+1))/(complexity g p:ℝ) := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hh.le
        have hpc : 1+(p:ℝ)+1 ≤ 2*((p:ℝ)+1) := by nlinarith only [Nat.cast_nonneg (α:=ℝ) p]
        have he1 := mul_le_mul_of_nonneg_left hpc hCp.le
        have he2 : 2*Cp+(3/2:ℝ)*Ct ≤ C := by dsimp [C];linarith
        have he3 := mul_le_mul_of_nonneg_right he2 (show (0:ℝ) ≤ (p:ℝ)+1 by positivity)
        nlinarith only [he1,he3]

lemma growing_marking_first_order_proof (P : PsiTheory) (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℕ,∀g p:ℕ,1 ≤ p → H ≤ complexity g p →
      (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) → ∀Y∈Icc (0:ℝ) y₀,
      (∀d:List ℕ,d.length=p → 0 ≤ 1-profile P g d Y ∧
        1-profile P g d Y ≤ min 1 (C*(d.sum:ℝ)*(d.sum+p+1)/(complexity g p:ℝ))) ∧
      |cuspCorrection P g p Y-1|+|genusCorrection P g p Y-1| ≤ C*((p:ℝ)+1)/(complexity g p:ℝ) := by
  obtain ⟨Cp,hCp,Hp,hP⟩ := growing_marking_profile_first_order_proof P M hM
  obtain ⟨Cc,hCc,Hc,hC⟩ := growing_marking_cusp_first_order_proof P M hM
  obtain ⟨Cg,hCg,Hg,hG⟩ := growing_marking_genus_first_order_proof P M hM
  let C : ℝ := Cp+Cc+Cg
  have hCpos : 0 < C := by dsimp [C];positivity
  refine ⟨C,hCpos,Hp+Hc+Hg,?_⟩
  intro g p hp hH hpM Y hY
  constructor
  · intro d hd
    have he := hP g p hp (by omega) hpM Y hY d hd
    refine ⟨he.1,he.2.trans ?_⟩
    apply min_le_min le_rfl
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hpc : Cp ≤ C := by dsimp [C];linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpc (by positivity)) (by positivity)
  · have hc := hC g p hp (by omega) hpM Y hY
    have hg := hG g p hp (by omega) hpM Y hY
    have he := add_le_add hc hg
    apply he.trans
    change Cc*((p:ℝ)+1)/(complexity g p:ℝ)+Cg*((p:ℝ)+1)/(complexity g p:ℝ) ≤ C*((p:ℝ)+1)/(complexity g p:ℝ)
    rw [←add_div,←add_mul]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp [C]
    linarith
end WP
