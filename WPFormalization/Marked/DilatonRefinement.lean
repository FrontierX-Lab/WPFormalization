import WPFormalization.Marked.CuspFromProfile
import WPFormalization.Marked.DilatonCorrection
import WPFormalization.Analysis.UniformKernelMoments
/-! Quantitative summation of the first degree expansion in the genuine dilaton identity.
The all-degree quartic remainder is an explicit helper input. The finite dimensional
zero convention and the proved absolute coefficient moments justify the infinite limit. -/
noncomputable section
open Set Filter
namespace WP
def dilatonBeta (p : ℕ) (Y : ℝ) : ℝ :=
  A Y*(((7-2*(p:ℝ))/4)*Theta Y-moment₁ Y+2-p)-1/2
lemma dilaton_A_abs_uniform : ∃ B : ℝ, 0<B ∧ ∀ Y ∈ Icc (0:ℝ) y₀, |A Y| ≤ B := by
  obtain ⟨B,hB,hbound⟩ := canonicalDilatonCoefficient_moment_tsum_uniform 0
  refine ⟨B,hB,?_⟩
  intro Y hY
  have hs : Summable (fun d : ℕ => |canonicalDilatonCoefficient Y d|) := by
    simpa only [pow_zero,one_mul] using canonicalDilatonCoefficient_moment_summable 0 Y hY
  have hn : |A Y| ≤ ∑' d : ℕ, |canonicalDilatonCoefficient Y d| := by
    rw [←(canonicalDilatonCoefficient_hasSum Y).tsum_eq]
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
      (show Summable (fun d : ℕ => ‖canonicalDilatonCoefficient Y d‖) by simpa only [Real.norm_eq_abs] using hs)
  exact hn.trans (by simpa only [pow_zero,one_mul] using hbound Y hY)
lemma dilaton_weight_moments_abs_uniform : ∃ B : ℝ, 0<B ∧ ∀ Y ∈ Icc (0:ℝ) y₀,
    |Theta Y| ≤ B ∧ |moment₁ Y| ≤ B := by
  obtain ⟨B,hB⟩ := uniform_kernel_moments.2 1
  refine ⟨max 1 B,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro Y hY
  have hθs := (Analysis.weight_hasSum_at_one Y hY).summable
  have hms := (Analysis.weight_first_moment_hasSum_at_one Y hY).summable
  have hs := (hB Y hY).1
  have hn := weight_nonneg Y hY
  have hθ : 0 ≤ Theta Y := tsum_nonneg hn
  have hm : 0 ≤ moment₁ Y := tsum_nonneg (fun n => mul_nonneg (Nat.cast_nonneg _) (hn n))
  rw [abs_of_nonneg hθ,abs_of_nonneg hm]
  constructor
  · exact ((hθs.tsum_le_tsum (fun n => by
        have := hn n
        simp only [pow_one]
        nlinarith [Nat.cast_nonneg (α:=ℝ) n]) hs).trans (hB Y hY).2).trans (le_max_right _ _)
  · exact ((hms.tsum_le_tsum (fun n => by
        have := hn n
        simp only [pow_one]
        nlinarith) hs).trans (hB Y hY).2).trans (le_max_right _ _)
lemma dilaton_correction_abs_uniform (p : ℕ) : ∃ B : ℝ, 0<B ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, |A Y*dilatonBeta p Y| ≤ B := by
  obtain ⟨a,ha,hA⟩ := dilaton_A_abs_uniform
  obtain ⟨m,hm,hM⟩ := dilaton_weight_moments_abs_uniform
  let R : ℝ := |(7-2*(p:ℝ))/4| * m+m+|2-(p:ℝ)|
  have hR : 0 ≤ R := by dsimp only [R];positivity
  refine ⟨a*(a*R+1/2)+1,by positivity,?_⟩
  intro Y hY
  have hf : |((7-2*(p:ℝ))/4)*Theta Y-moment₁ Y+2-p| ≤ R := by
    have he : ((7-2*(p:ℝ))/4)*Theta Y-moment₁ Y+2-p=
        (((7-2*(p:ℝ))/4)*Theta Y-moment₁ Y)+(2-p) := by ring
    rw [he]
    calc _  ≤  |((7-2*(p:ℝ))/4)*Theta Y-moment₁ Y|+|2-(p:ℝ)| := abs_add_le _ _
         _  ≤  (|((7-2*(p:ℝ))/4)*Theta Y|+|moment₁ Y|)+|2-(p:ℝ)| :=
           add_le_add_left (abs_sub _ _) _
         _  ≤  (|(7-2*(p:ℝ))/4| * m+m)+|2-(p:ℝ)| := by
           rw [abs_mul]
           exact add_le_add_left (add_le_add
             (mul_le_mul_of_nonneg_left (hM Y hY).1 (abs_nonneg _)) (hM Y hY).2) _
         _ = R := rfl
  have hb : |dilatonBeta p Y| ≤ a*R+1/2 := by
    unfold dilatonBeta
    calc _  ≤  |A Y*(((7-2*(p:ℝ))/4)*Theta Y-moment₁ Y+2-p)|+|(1/2:ℝ)| := abs_sub _ _
         _ = |A Y| * |((7-2*(p:ℝ))/4)*Theta Y-moment₁ Y+2-p|+1/2 := by rw [abs_mul];norm_num
         _  ≤  a*R+1/2 := add_le_add_left (mul_le_mul (hA Y hY) hf (abs_nonneg _) ha.le) _
  rw [abs_mul]
  exact (mul_le_mul (hA Y hY) hb (abs_nonneg _) ha.le).trans (by linarith)

lemma refined_cusp_child_of_profile (P : PsiTheory) (p G : ℕ) (Q : ℝ) (hQ : 0<Q)
    (hprofile : ∀ g ≥ G, ∀ d : List ℕ, d.length=p+1 → ∀ Y ∈ Icc (0:ℝ) y₀,
      |profile P g d Y-(1-degreeCorrection d Y/(complexity g (p+1):ℝ))| ≤
        Q*((d.sum:ℝ)+1)^4/(complexity g (p+1):ℝ)^2) :
    ∃ C : ℝ, 0<C ∧ ∀ g ≥ G, 2 ≤ g → ∀ Y ∈ Icc (0:ℝ) y₀,
      |(complexity g p:ℝ)*W P g p Y/W P g (p+1) Y-
        (A Y-A Y*dilatonBeta p Y/(complexity g (p+1):ℝ))| ≤
          C/(complexity g (p+1):ℝ)^2 := by
  obtain ⟨M,hM,hmoment⟩ := canonicalDilatonCoefficient_succ_moment_abs_sum_uniform 4
  refine ⟨Q*M,by positivity,?_⟩
  intro g hg hg₂ Y hY
  have hs : Stable g p := by unfold Stable;omega
  have hh : 0<(complexity g (p+1):ℝ) := by
    exact_mod_cast (show 0<complexity g (p+1) by unfold complexity;omega)
  let h : ℝ := complexity g (p+1)
  let R := (complexity g p:ℝ)*W P g p Y/W P g (p+1) Y
  let f := fun d : ℕ => canonicalDilatonCoefficient Y d*(1-degreeCorrection (d::List.replicate p 0) Y/h)
  have hδ : HasSum (fun d : ℕ => canonicalDilatonCoefficient Y d*degreeCorrection (d::List.replicate p 0) Y)
      (A Y*dilatonBeta p Y) := by
    simpa only [dilatonBeta] using canonicalDilaton_degreeCorrection_hasSum p Y hY
  have hf : HasSum f (A Y-A Y*dilatonBeta p Y/h) := by
    have ht := (canonicalDilatonCoefficient_hasSum Y).sub (hδ.div_const h)
    convert! ht using 1
    ext d
    dsimp only [f]
    ring
  have hfzero : f 0=0 := by dsimp [f];simp [canonicalDilatonCoefficient]
  have hfs : HasSum (fun n : ℕ => f (n+1)) (A Y-A Y*dilatonBeta p Y/h) := by
    apply (hasSum_nat_add_iff (f:=f) 1).mpr
    simpa only [Finset.sum_range_one,hfzero,add_zero] using hf
  have herr (N : ℕ) (hN : dimension g (p+1) ≤ N) :
      |R-∑ n ∈ Finset.range N, f (n+1)| ≤ Q*M/h^2 := by
    have hext := canonical_profile_sum_extended_stable P g p N hs hN Y hY
    have heq : R-∑ n ∈ Finset.range N, f (n+1)=
        ∑ n ∈ Finset.range N, canonicalDilatonCoefficient Y (n+1)*
          (profile P g ((n+1)::List.replicate p 0) Y-
            (1-degreeCorrection ((n+1)::List.replicate p 0) Y/h)) := by
      change R=∑ n ∈ Finset.range N, canonicalDilatonCoefficient Y (n+1)*
        profile P g ((n+1)::List.replicate p 0) Y at hext
      rw [hext,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [f]
      ring
    rw [heq]
    calc _  ≤  ∑ n ∈ Finset.range N, |canonicalDilatonCoefficient Y (n+1)*
            (profile P g ((n+1)::List.replicate p 0) Y-
              (1-degreeCorrection ((n+1)::List.replicate p 0) Y/h))| := Finset.abs_sum_le_sum_abs _ _
         _  ≤  ∑ n ∈ Finset.range N, (Q/h^2)*(((n:ℝ)+2)^4* |canonicalDilatonCoefficient Y (n+1)|) := by
           apply Finset.sum_le_sum
           intro n hn
           have hp := hprofile g hg ((n+1)::List.replicate p 0) (by simp) Y hY
           simp only [List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,Nat.cast_add,Nat.cast_one] at hp
           rw [abs_mul]
           have he := mul_le_mul_of_nonneg_left hp (abs_nonneg (canonicalDilatonCoefficient Y (n+1)))
           convert he using 1 <;> dsimp only [h] <;> ring
         _ = (Q/h^2)*(∑ n ∈ Finset.range N, ((n:ℝ)+2)^4* |canonicalDilatonCoefficient Y (n+1)|) :=
           (Finset.mul_sum _ _ _).symm
         _  ≤  (Q/h^2)*M := mul_le_mul_of_nonneg_left (hmoment Y hY N) (by positivity)
         _ = _ := by ring
  have ht : Tendsto (fun N : ℕ => |R-∑ n ∈ Finset.range N, f (n+1)|)
      atTop (nhds |R-(A Y-A Y*dilatonBeta p Y/h)|) :=
    (tendsto_const_nhds.sub hfs.tendsto_sum_nat).abs
  exact le_of_tendsto ht (eventually_atTop.mpr ⟨dimension g (p+1),fun N hN=>herr N hN⟩)

lemma refined_cusp_change_complexity (x a b h c B : ℝ) (hh : 0<h)
    (hc : 0 ≤ c) (hb : |b| ≤ B)
    (hx : |x-(a-b/(h+1))| ≤ c/(h+1)^2) :
    |x-(a-b/h)| ≤ (c+B)/h^2 := by
  have hhp : 0<h+1 := by linarith
  have hB : 0 ≤ B := (abs_nonneg _).trans hb
  have he : x-(a-b/h)=(x-(a-b/(h+1)))+b/(h*(h+1)) := by
    field_simp;ring
  have hc' : c/(h+1)^2 ≤ c/h^2 :=
    div_le_div_of_nonneg_left hc (sq_pos_of_pos hh) (by nlinarith)
  have hb' : B/(h*(h+1)) ≤ B/h^2 :=
    div_le_div_of_nonneg_left hB (sq_pos_of_pos hh) (by nlinarith)
  rw [he]
  calc _ ≤ |x-(a-b/(h+1))|+|b/(h*(h+1))| := abs_add_le _ _
       _ = |x-(a-b/(h+1))|+|b|/(h*(h+1)) := by rw [abs_div,abs_of_pos (mul_pos hh hhp)]
       _ ≤ c/(h+1)^2+B/(h*(h+1)) :=
         add_le_add hx (div_le_div_of_nonneg_right hb (mul_pos hh hhp).le)
       _ ≤ c/h^2+B/h^2 := add_le_add hc' hb'
       _ = _ := by ring
lemma refined_cusp_of_profile (P : PsiTheory) (p G : ℕ) (Q : ℝ) (hQ : 0<Q)
    (hprofile : ∀ g ≥ G, ∀ d : List ℕ, d.length=p+1 → ∀ Y ∈ Icc (0:ℝ) y₀,
      |profile P g d Y-(1-degreeCorrection d Y/(complexity g (p+1):ℝ))| ≤
        Q*((d.sum:ℝ)+1)^4/(complexity g (p+1):ℝ)^2) :
    ∃ C : ℝ, 0<C ∧ ∃ G' : ℕ, ∀ g ≥ G', ∀ Y ∈ Icc (0:ℝ) y₀,
      |(complexity g p:ℝ)*W P g p Y/W P g (p+1) Y-
        A Y*(1-dilatonBeta p Y/(complexity g p:ℝ))| ≤
          C/(complexity g p:ℝ)^2 := by
  obtain ⟨c,hc,hchild⟩ := refined_cusp_child_of_profile P p G Q hQ hprofile
  obtain ⟨B,hB,hβ⟩ := dilaton_correction_abs_uniform p
  refine ⟨c+B,by positivity,2+G,?_⟩
  intro g hg Y hY
  have hh : 0<(complexity g p:ℝ) := by
    exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have he := hchild g (by omega) (by omega) Y hY
  have hs : complexity g (p+1)=complexity g p+1 := by unfold complexity;omega
  rw [hs,Nat.cast_add,Nat.cast_one] at he
  have hi := refined_cusp_change_complexity _ (A Y) (A Y*dilatonBeta p Y)
    (complexity g p) c B hh hc.le (hβ Y hY) he
  have heq : A Y*(1-dilatonBeta p Y/(complexity g p:ℝ))=
      A Y-A Y*dilatonBeta p Y/(complexity g p:ℝ) := by ring
  rw [heq]
  exact hi
end WP
