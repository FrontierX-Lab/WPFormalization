import WPFormalization.Marked.GrowingProfileChildren
import WPFormalization.Marked.SingleMarkingProfile

/-! The genuine first-order profile estimate is uniform for growing marking counts and every degree tuple, with the original min-one bound. -/
noncomputable section
namespace WP
open Set
lemma profile_growing_markings_genus_bound (P : PsiTheory) (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ,0 < C ∧ ∃ G : ℕ,∀g≥G,∀p:ℕ,1 ≤ p →
      (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) → ∀d:List ℕ,d.length=p →
      ∀Y∈Icc (0:ℝ) y₀,0 ≤ 1-profile P g d Y ∧
        1-profile P g d Y ≤ C*(d.sum:ℝ)*(d.sum+p+1)/(g:ℝ) := by
  obtain ⟨Ca,hCa,Ga,hA⟩ := profile_adjacent_growing_markings_bound P M hM
  obtain ⟨Co,hCo,hO⟩ := quadratic_profile_one_proof P
  let C : ℝ := Ca+Co
  have hC : 0 < C := by dsimp [C];positivity
  have hCaC : Ca ≤ C := by dsimp [C];linarith
  have hCoC : Co ≤ C := by dsimp [C];linarith
  refine ⟨C,hC,Ga+2,?_⟩
  intro g hg p hp hpM d hd Y hY
  have hg2 : 2 ≤ g := by omega
  have hgR : (0:ℝ) < g := by exact_mod_cast (show 0<g by omega)
  by_cases hp1 : p=1
  · rcases hp1 with rfl
    have he := hO g (by omega) d hd Y hY
    refine ⟨he.1,he.2.trans ?_⟩
    norm_num only [Nat.cast_one]
    apply div_le_div_of_nonneg_right _ hgR.le
    calc
      _ ≤ C*(d.sum:ℝ)*(d.sum+1) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCoC (by positivity)) (by positivity)
      _ ≤ C*(d.sum:ℝ)*(d.sum+1+1) := by nlinarith only [mul_nonneg hC.le (Nat.cast_nonneg (α:=ℝ) d.sum)]
  · have he := profile_linear_size_of_adjacent P g p hp (by unfold Stable;omega) (by omega)
      Y hY Ca hCa.le (fun k e he=>hA g (by omega) p (by omega) hpM k e he Y hY) d hd
    refine ⟨he.1,he.2.trans ?_⟩
    apply div_le_div_of_nonneg_right _ hgR.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCaC (by positivity)) (by positivity)

lemma growing_marking_profile_first_order_proof (P : PsiTheory) (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ,0 < C ∧ ∃ H : ℕ,∀g p:ℕ,1 ≤ p → H ≤ complexity g p →
      (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) → ∀Y∈Icc (0:ℝ) y₀,
      ∀d:List ℕ,d.length=p → 0 ≤ 1-profile P g d Y ∧
        1-profile P g d Y ≤ min 1 (C*(d.sum:ℝ)*(d.sum+p+1)/(complexity g p:ℝ)) := by
  obtain ⟨Q,hQ,G,hprofile⟩ := profile_growing_markings_genus_bound P M hM
  obtain ⟨H,hH⟩ := exists_nat_ge (max (4*M^2+1) (4*((G+2:ℕ):ℝ)))
  refine ⟨4*Q,by positivity,H,?_⟩
  intro g p hp hlarge hpM Y hY d hd
  have hHh : (H:ℝ) ≤ complexity g p := by exact_mod_cast hlarge
  have hhM : 4*M^2+1 ≤ (complexity g p:ℝ) := (le_max_left _ _).trans (hH.trans hHh)
  have hhG : 4*((G+2:ℕ):ℝ) ≤ complexity g p := (le_max_right _ _).trans (hH.trans hHh)
  have hh : (0:ℝ) < complexity g p := by nlinarith only [hhM,sq_nonneg M]
  have hs : Stable g p := by
    have he : 0 < complexity g p := by exact_mod_cast hh
    unfold complexity Stable at *
    omega
  have hcomp := complexity_le_four_genus_growing g p hs M hM hpM hhM
  have hgAll : G+2 ≤ g := by exact_mod_cast (show ((G+2:ℕ):ℝ) ≤ g by linarith only [hhG,hcomp])
  have hgR : (0:ℝ) < g := by exact_mod_cast (show 0<g by omega)
  have he := hprofile g (by omega) p hp hpM d hd Y hY
  have hb := normalized_profile_bounds P g d (by rwa [hd]) (by omega) Y hY
  refine ⟨he.1,le_min ?_ (he.2.trans ?_)⟩
  · change 1-(normalized P g d Y/normalized P g (List.replicate d.length 0) Y) ≤ 1
    linarith only [hb.1]
  · apply (div_le_div_iff₀ hgR hh).mpr
    have hf := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ Q*(d.sum:ℝ)*(d.sum+p+1) by positivity)
    nlinarith only [hf]
end WP
