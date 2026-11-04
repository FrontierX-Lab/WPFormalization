import WPFormalization.Analysis.CanonicalCoordinatePath
import WPFormalization.Marked.SecondDegreeAdjacent

/-! A finite canonical-path sum propagates the proved adjacent errors to the existing secondProfile definition. -/

noncomputable section
open Set

namespace WP
lemma second_profile_canonical_small (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) (g : ℕ) (hg : 1 ≤ g)
    (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ e : List ℕ,e.length=p → (e.sum:ℝ) ≤ (complexity g p:ℝ)/2 →
      ∀ i : ℕ,i<e.length →
        |(profile P g e Y-profile P g (HigherOrder.raiseDegree e i) Y)-
          (degreeCorrection (HigherOrder.raiseDegree e i) Y-degreeCorrection e Y)/(complexity g p:ℝ)-
          HigherOrder.secondIncrement Y i e/(complexity g p:ℝ)^2| ≤
          C*((e.sum:ℝ)+1)^5/(complexity g p:ℝ)^3) :
    ∀ d : List ℕ,d.length=p → (d.sum:ℝ) ≤ (complexity g p:ℝ)/2 →
      |profile P g d Y-(1-degreeCorrection d Y/(complexity g p:ℝ)+
        HigherOrder.secondProfile Y d/(complexity g p:ℝ)^2)| ≤
          C*((d.sum:ℝ)+1)^6/(complexity g p:ℝ)^3 := by
  intro d hd hsmall
  let h : ℝ := complexity g p
  let F (e : List ℕ) : ℝ := profile P g e Y+degreeCorrection e Y/h
  let rem (i t : ℕ) : ℝ :=
    F (HigherOrder.beforeCoordinate d i t)-F (HigherOrder.beforeCoordinate d i (t+1))-
      HigherOrder.secondIncrement Y i (HigherOrder.beforeCoordinate d i t)/h^2
  have hhp : 0<h := by dsimp [h];exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hterm (i : ℕ) (hi : i∈Finset.range d.length) (t : ℕ) (ht : t∈Finset.range d[i]!) :
      |rem i t| ≤ C*((d.sum:ℝ)+1)^5/h^3 := by
    have hi' := Finset.mem_range.mp hi
    have ht' := Finset.mem_range.mp ht
    have hlen : (HigherOrder.beforeCoordinate d i t).length=p := by rw [HigherOrder.beforeCoordinate_length,hd]
    have hsum := HigherOrder.beforeCoordinate_sum_le d i t hi' ht'.le
    have hsumR : ((HigherOrder.beforeCoordinate d i t).sum:ℝ) ≤ d.sum := by exact_mod_cast hsum
    have he := hstep _ hlen (hsumR.trans hsmall) i (by rw [HigherOrder.beforeCoordinate_length];exact hi')
    rw [HigherOrder.raiseDegree_beforeCoordinate d i t hi'] at he
    have hrem : rem i t=
        (profile P g (HigherOrder.beforeCoordinate d i t) Y-
          profile P g (HigherOrder.beforeCoordinate d i (t+1)) Y)-
        (degreeCorrection (HigherOrder.beforeCoordinate d i (t+1)) Y-
          degreeCorrection (HigherOrder.beforeCoordinate d i t) Y)/h-
        HigherOrder.secondIncrement Y i (HigherOrder.beforeCoordinate d i t)/h^2 := by dsimp [rem,F];ring
    rw [hrem]
    exact he.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add hsumR le_rfl) 5) hC) (by positivity))
  have hsum : (∑ i∈Finset.range d.length,∑ t∈Finset.range d[i]!,rem i t)=
      F (List.replicate d.length 0)-F d+HigherOrder.secondProfile Y d/h^2 := by
    calc
      _ = (∑ i∈Finset.range d.length,∑ t∈Finset.range d[i]!,
          (F (HigherOrder.beforeCoordinate d i t)-F (HigherOrder.beforeCoordinate d i (t+1))))-
          (∑ i∈Finset.range d.length,∑ t∈Finset.range d[i]!,
            HigherOrder.secondIncrement Y i (HigherOrder.beforeCoordinate d i t))/h^2 := by
        rw [Finset.sum_div,←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_div,←Finset.sum_sub_distrib]
      _ = _ := by
        rw [HigherOrder.canonical_coordinate_path_sum_reverse]
        unfold HigherOrder.secondProfile
        ring
  have hF0 : F (List.replicate d.length 0)=1 := by
    dsimp [F]
    rw [hd,profile_replicate_zero P g p hp (by unfold Stable;omega) Y hY,
      HigherOrder.degreeCorrection_zero_tuple]
    ring
  have heq : profile P g d Y-(1-degreeCorrection d Y/h+HigherOrder.secondProfile Y d/h^2)=
      -(∑ i∈Finset.range d.length,∑ t∈Finset.range d[i]!,rem i t) := by
    rw [hsum,hF0]
    dsimp [F]
    ring
  rw [heq,abs_neg]
  have hlookup : (∑i∈Finset.range d.length,(d[i]!:ℝ))=(d.sum:ℝ) := by
    rw [sum_range_getElem]
    exact (map_list_sum (Nat.castAddMonoidHom ℝ) d).symm
  calc
    _ ≤ ∑i∈Finset.range d.length,|∑t∈Finset.range d[i]!,rem i t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑i∈Finset.range d.length,∑t∈Finset.range d[i]!,|rem i t| :=
      Finset.sum_le_sum (fun i hi => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑i∈Finset.range d.length,∑t∈Finset.range d[i]!,C*((d.sum:ℝ)+1)^5/h^3 :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun t ht => hterm i hi t ht))
    _ = (d.sum:ℝ)*(C*((d.sum:ℝ)+1)^5/h^3) := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw [←Finset.sum_mul,hlookup]
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right (show (d.sum:ℝ) ≤ (d.sum:ℝ)+1 by linarith)
        (show 0 ≤ C*((d.sum:ℝ)+1)^5/h^3 by positivity)
      convert hm using 1 <;> ring
end WP
