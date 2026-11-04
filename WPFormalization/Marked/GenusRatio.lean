import WPFormalization.Marked.Positivity
import WPFormalization.Statements.QuadraticProfile
import WPFormalization.Statements.MarkedSeparating
/-! The normalized genuine KdV identity and the original genus-exchange estimate. -/
noncomputable section
open Set Filter
namespace WP
lemma normalized_kdv_profile (P : PsiTheory) (g p : ℕ) (hg : 1 ≤ g) (hp : 2 ≤ p)
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    profile P g (1::List.replicate (p-1) 0) Y =
      W P (g-1) (p+2) Y/W P g p Y+(3/2 : ℝ)*separatingT P g p Y := by
  have hs : Stable g p := by unfold Stable; omega
  have hU : 0 < normalized P g (List.replicate p 0) Y :=
    normalized_pos_valid_nonempty P g _ (by simp; omega) (by simpa using hs) (by simp) Y hY
  have hW : (4 : ℝ)^g ≠ 0 := by positivity
  have hpow : (4 : ℝ)^g=(4 : ℝ)^(g-1)*4 := by rw [←pow_succ,Nat.sub_add_cancel hg]
  have hsep : (∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (p-1),
      (Nat.choose (p-2) s : ℝ)*W P j (s+2) Y*W P (g-j) (p-s) Y) =
      (4 : ℝ)^g*(∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (p-1),
        (Nat.choose (p-2) s : ℝ)*normalized P j (List.replicate (s+2) 0) Y*
          normalized P (g-j) (List.replicate (p-s) 0) Y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hj' := Finset.mem_range.mp hj
    have he : (4 : ℝ)^j*(4 : ℝ)^(g-j)=(4 : ℝ)^g := by rw [←pow_add,Nat.add_sub_of_le (by omega)]
    unfold W
    calc
      _ = ((4 : ℝ)^j*(4 : ℝ)^(g-j))*
          ((Nat.choose (p-2) s : ℝ)*normalized P j (List.replicate (s+2) 0) Y*
            normalized P (g-j) (List.replicate (p-s) 0) Y) := by ring
      _ = _ := by rw [he]
  have hk := shifted_kdv P g p hg hp Y hY
  unfold profile separatingT
  have hlen : (1::List.replicate (p-1) 0).length=p := by simp; omega
  rw [hlen,hsep]
  unfold W
  rw [hk,hpow]
  field_simp [hU.ne',show (4 : ℝ)^(g-1) ≠ 0 by positivity]
  <;> ring
lemma marked_genus_proof (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |W P (g-1) (p+2) Y/W P g p Y-1| ≤ C/g := by
  obtain ⟨C,hC,hquad⟩ := quadratic_profile P p hp
  obtain ⟨B,hB,g₀,hsep⟩ := separating_estimates P p hp
  refine ⟨2*C+(3/2 : ℝ)*B,by positivity,max g₀ 1,?_⟩
  intro g hg Y hY
  have hg₁ : 1 ≤ g := (le_max_right _ _).trans hg
  have hg₀ : g₀ ≤ g := (le_max_left _ _).trans hg
  have hq := hquad g hg₁ (1::List.replicate (p-1) 0) (by simp; omega) Y hY
  have hs := (hsep g hg₀ Y hY).2
  simp only [List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,Nat.cast_one] at hq
  have hid := normalized_kdv_profile P g p hg₁ hp Y hY
  have hidentity : W P (g-1) (p+2) Y/W P g p Y-1 =
      (profile P g (1::List.replicate (p-1) 0) Y-1)-(3/2 : ℝ)*separatingT P g p Y := by linarith
  rw [hidentity]
  calc
    _ ≤ |profile P g (1::List.replicate (p-1) 0) Y-1|+|(3/2 : ℝ)*separatingT P g p Y| := abs_sub _ _
    _ = (1-profile P g (1::List.replicate (p-1) 0) Y)+(3/2 : ℝ)*|separatingT P g p Y| := by
      rw [abs_sub_comm,abs_of_nonneg hq.1,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3/2)]
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤3/2)
      have he := add_le_add hq.2 hb
      convert he using 1 <;> ring
end WP
