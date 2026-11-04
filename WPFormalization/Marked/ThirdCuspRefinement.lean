import WPFormalization.Marked.SecondProfileProof
import WPFormalization.HigherOrder.SecondDilatonMoment
import WPFormalization.Marked.DilatonRefinement
import WPFormalization.Analysis.ThirdCuspAlgebra

/-! The genuine second profile summed in the dilaton identity gives the third-order cusp ratio. All marking counts, including zero, are covered. -/

noncomputable section
open Set Filter

namespace WP
lemma third_cusp_child_of_profile (P : PsiTheory) (p G : ℕ) (Q : ℝ) (hQ : 0<Q)
    (hprofile : ∀ g ≥ G,∀ d : List ℕ,d.length=p+1 →∀ Y∈Icc (0:ℝ) y₀,
      |profile P g d Y-(1-degreeCorrection d Y/(complexity g (p+1):ℝ)+
        HigherOrder.secondProfile Y d/(complexity g (p+1):ℝ)^2)| ≤
        Q*((d.sum:ℝ)+1)^6/(complexity g (p+1):ℝ)^3) :
    ∃ C : ℝ,0<C ∧ ∀ g ≥ G,2 ≤ g →∀ Y∈Icc (0:ℝ) y₀,
      |(complexity g p:ℝ)*W P g p Y/W P g (p+1) Y-
        (A Y-A Y*transportBeta p Y/(complexity g (p+1):ℝ)+
          HigherOrder.secondDilatonMoment p Y/(complexity g (p+1):ℝ)^2)| ≤
            C/(complexity g (p+1):ℝ)^3 := by
  obtain ⟨M,hM,hmoment⟩ := canonicalDilatonCoefficient_succ_moment_abs_sum_uniform 6
  refine ⟨Q*M,by positivity,?_⟩
  intro g hg hg2 Y hY
  have hs : Stable g p := by unfold Stable;omega
  have hhp : (0:ℝ)<complexity g (p+1) := by exact_mod_cast (show 0<complexity g (p+1) by unfold complexity;omega)
  let h : ℝ := complexity g (p+1)
  let R : ℝ := (complexity g p:ℝ)*W P g p Y/W P g (p+1) Y
  let f (d : ℕ) : ℝ := canonicalDilatonCoefficient Y d*
    (1-degreeCorrection (d::List.replicate p 0) Y/h+HigherOrder.secondProfile Y (d::List.replicate p 0)/h^2)
  have hδ : HasSum (fun d : ℕ => canonicalDilatonCoefficient Y d*degreeCorrection (d::List.replicate p 0) Y)
      (A Y*transportBeta p Y) := by
    simpa only [transportBeta] using canonicalDilaton_degreeCorrection_hasSum p Y hY
  have he := HigherOrder.secondDilatonMoment_hasSum p Y hY
  have hf : HasSum f (A Y-A Y*transportBeta p Y/h+HigherOrder.secondDilatonMoment p Y/h^2) := by
    have ht := ((canonicalDilatonCoefficient_hasSum Y).sub (hδ.div_const h)).add (he.div_const (h^2))
    convert ht using 1
    funext d
    dsimp [f]
    ring
  have hfzero : f 0=0 := by dsimp [f];simp [canonicalDilatonCoefficient]
  have hfs : HasSum (fun n : ℕ => f (n+1))
      (A Y-A Y*transportBeta p Y/h+HigherOrder.secondDilatonMoment p Y/h^2) := by
    apply (hasSum_nat_add_iff (f := f) 1).mpr
    simpa only [Finset.sum_range_one,hfzero,add_zero] using hf
  have herr (N : ℕ) (hN : dimension g (p+1) ≤ N) :
      |R-∑ n∈Finset.range N,f (n+1)| ≤ Q*M/h^3 := by
    have hext := canonical_profile_sum_extended_stable P g p N hs hN Y hY
    have heq : R-∑ n∈Finset.range N,f (n+1)=
        ∑ n∈Finset.range N,canonicalDilatonCoefficient Y (n+1)*
          (profile P g ((n+1)::List.replicate p 0) Y-
            (1-degreeCorrection ((n+1)::List.replicate p 0) Y/h+
              HigherOrder.secondProfile Y ((n+1)::List.replicate p 0)/h^2)) := by
      change R=∑ n∈Finset.range N,canonicalDilatonCoefficient Y (n+1)*
        profile P g ((n+1)::List.replicate p 0) Y at hext
      rw [hext,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [f]
      ring
    rw [heq]
    calc
      _ ≤ ∑ n∈Finset.range N,|canonicalDilatonCoefficient Y (n+1)*
          (profile P g ((n+1)::List.replicate p 0) Y-
            (1-degreeCorrection ((n+1)::List.replicate p 0) Y/h+
              HigherOrder.secondProfile Y ((n+1)::List.replicate p 0)/h^2))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n∈Finset.range N,(Q/h^3)*(((n:ℝ)+2)^6*|canonicalDilatonCoefficient Y (n+1)|) := by
        apply Finset.sum_le_sum
        intro n hn
        have hp := hprofile g hg ((n+1)::List.replicate p 0) (by simp) Y hY
        simp only [List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,Nat.cast_add,Nat.cast_one] at hp
        rw [abs_mul]
        have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (canonicalDilatonCoefficient Y (n+1)))
        convert hm using 1 <;> dsimp [h] <;> ring
      _ = (Q/h^3)*(∑ n∈Finset.range N,((n:ℝ)+2)^6*|canonicalDilatonCoefficient Y (n+1)|) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (Q/h^3)*M := mul_le_mul_of_nonneg_left (hmoment Y hY N) (by positivity)
      _ = _ := by ring
  have ht : Tendsto (fun N : ℕ => |R-∑ n∈Finset.range N,f (n+1)|) atTop
      (nhds |R-(A Y-A Y*transportBeta p Y/h+HigherOrder.secondDilatonMoment p Y/h^2)|) :=
    (tendsto_const_nhds.sub hfs.tendsto_sum_nat).abs
  exact le_of_tendsto ht (eventually_atTop.mpr ⟨dimension g (p+1),fun N hN => herr N hN⟩)
end WP

namespace WP
lemma marked_cusp_third_order_proof (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y∈Icc (0:ℝ) y₀,
      |(complexity g p:ℝ)*W P g p Y/W P g (p+1) Y-
        (A Y-A Y*transportBeta p Y/(complexity g p:ℝ)+
          (A Y*transportBeta p Y+HigherOrder.secondDilatonMoment p Y)/(complexity g p:ℝ)^2)| ≤
            C/(complexity g p:ℝ)^3 := by
  obtain ⟨Q,hQ,G,hprofile⟩ := second_profile_all_degrees_proof P (p+1) (by omega)
  obtain ⟨Cr,hCr,hraw⟩ := third_cusp_child_of_profile P p G Q hQ hprofile
  obtain ⟨B,hB,hb⟩ := dilaton_correction_abs_uniform p
  obtain ⟨E,hE,he⟩ := HigherOrder.secondDilatonMoment_abs_uniform p
  refine ⟨Cr+B+3*E,by positivity,max G 2,?_⟩
  intro g hg Y hY
  have hgG : G ≤ g := (le_max_left _ _).trans hg
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  have hh : (1:ℝ) ≤ complexity g p := by exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega)
  have hcomp : (complexity g (p+1):ℝ)=(complexity g p:ℝ)+1 := by
    exact_mod_cast (show complexity g (p+1)=complexity g p+1 by unfold complexity;omega)
  have hr := hraw g hgG hg2 Y hY
  rw [hcomp] at hr
  have hb' : |A Y*transportBeta p Y| ≤ B := by simpa only [transportBeta,dilatonBeta] using hb Y hY
  exact Analysis.third_cusp_change_complexity _ _ _ _ _ Cr B E hh hCr.le hB.le hE.le hb' (he Y hY) hr
end WP
