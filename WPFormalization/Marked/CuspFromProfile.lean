import WPFormalization.Marked.Positivity
import WPFormalization.Marked.DilatonMoments
/-! Stable finite dilaton identities and the exact quadratic-profile error transport. -/
noncomputable section
open Set Filter
namespace WP
lemma canonical_dilaton_profile_sum_stable (P : PsiTheory) (g p : ℕ) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    (complexity g p : ℝ)*W P g p Y/W P g (p+1) Y =
      ∑ n ∈ Finset.range (dimension g (p+1)), canonicalDilatonCoefficient Y (n+1)*
        profile P g ((n+1)::List.replicate p 0) Y := by
  have hU : 0 < normalized P g (List.replicate (p+1) 0) Y :=
    normalized_pos_valid_nonempty P g _ (by simp only [List.length_replicate]; omega)
      (by simp only [List.length_replicate]; unfold Stable at hs ⊢; omega) (by simp) Y hY
  have hd := canonical_shifted_dilaton_closed P g p hs Y hY
  rw [Finset.sum_range_succ'] at hd
  have hzero : canonicalDilatonCoefficient Y 0=0 := by simp [canonicalDilatonCoefficient]
  simp only [hzero,zero_mul,add_zero] at hd
  have hsum : (∑ n ∈ Finset.range (dimension g (p+1)), canonicalDilatonCoefficient Y (n+1)*
      profile P g ((n+1)::List.replicate p 0) Y) =
      (∑ n ∈ Finset.range (dimension g (p+1)), canonicalDilatonCoefficient Y (n+1)*
        normalized P g ((n+1)::List.replicate p 0) Y)/normalized P g (List.replicate (p+1) 0) Y := by
    unfold profile
    simp only [List.length_cons,List.length_replicate]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hsum,← hd]
  unfold W
  field_simp [hU.ne',show (4 : ℝ)^g ≠ 0 by positivity]
  <;> ring
lemma profile_excess_zero (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ)
    (hd : dimension g d.length<d.sum) : profile P g d Y=0 := by
  unfold profile
  rw [normalized_excess P g d Y hd,zero_div]
lemma canonical_profile_sum_extended_stable (P : PsiTheory) (g p N : ℕ) (hs : Stable g p)
    (hN : dimension g (p+1) ≤ N) (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    (complexity g p : ℝ)*W P g p Y/W P g (p+1) Y =
      ∑ n ∈ Finset.range N, canonicalDilatonCoefficient Y (n+1)*
        profile P g ((n+1)::List.replicate p 0) Y := by
  rw [canonical_dilaton_profile_sum_stable P g p hs Y hY]
  apply Finset.sum_subset (Finset.range_mono hN)
  intro n hn hn'
  have hdim : dimension g (p+1) ≤ n := by
    have hnot : ¬n<dimension g (p+1) := by simpa only [Finset.mem_range] using hn'
    omega
  have hexcess : dimension g ((n+1)::List.replicate p 0).length<((n+1)::List.replicate p 0).sum := by
    simp only [List.length_cons,List.length_replicate,List.sum_cons,List.sum_replicate,nsmul_zero,add_zero]
    omega
  rw [profile_excess_zero P g _ Y hexcess,mul_zero]
lemma cusp_estimate_of_quadratic (P : PsiTheory) (p : ℕ) (Q : ℝ) (hQ : 0<Q)
    (hquad : ∀ g : ℕ, 1≤g → ∀ d : List ℕ, d.length=p+1 → ∀ Y ∈ Icc (0:ℝ) y₀,
      0≤1-profile P g d Y ∧ 1-profile P g d Y≤Q*(d.sum : ℝ)*(d.sum+1)/g) :
    ∃ C : ℝ, 0<C ∧ ∀ g : ℕ, 1≤g → Stable g p → ∀ Y ∈ Icc (0:ℝ) y₀,
      |(complexity g p : ℝ)*W P g p Y/W P g (p+1) Y-A Y|≤C/g := by
  obtain ⟨M,hM,hmoment⟩ := canonicalDilatonCoefficient_succ_quadratic_abs_sum_uniform
  refine ⟨Q*M,by positivity,?_⟩
  intro g hg hs Y hY
  have hgR : (0 : ℝ)<g := by exact_mod_cast (show 0<g by omega)
  let R := (complexity g p : ℝ)*W P g p Y/W P g (p+1) Y
  have herror (N : ℕ) (hN : dimension g (p+1)≤N) :
      |R-(∑ n ∈ Finset.range N, canonicalDilatonCoefficient Y (n+1))| ≤ Q*M/g := by
    have hext := canonical_profile_sum_extended_stable P g p N hs hN Y hY
    have heq : R-(∑ n ∈ Finset.range N, canonicalDilatonCoefficient Y (n+1)) =
        ∑ n ∈ Finset.range N, canonicalDilatonCoefficient Y (n+1)*
          (profile P g ((n+1)::List.replicate p 0) Y-1) := by
      change R=∑ n ∈ Finset.range N, canonicalDilatonCoefficient Y (n+1)*
        profile P g ((n+1)::List.replicate p 0) Y at hext
      rw [hext,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [heq]
    calc
      _ ≤ ∑ n ∈ Finset.range N, |canonicalDilatonCoefficient Y (n+1)*
          (profile P g ((n+1)::List.replicate p 0) Y-1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range N, (Q/(g : ℝ))*(((n : ℝ)+2)^2*|canonicalDilatonCoefficient Y (n+1)|) := by
        apply Finset.sum_le_sum
        intro n hn
        have hq := hquad g hg ((n+1)::List.replicate p 0) (by simp) Y hY
        simp only [List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,Nat.cast_add,Nat.cast_one] at hq
        have hpoly : ((n : ℝ)+1)*((n : ℝ)+1+1)≤((n : ℝ)+2)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
        have hbig : 1-profile P g ((n+1)::List.replicate p 0) Y≤(Q/(g : ℝ))*((n : ℝ)+2)^2 := by
          calc
            _ ≤ Q*((n : ℝ)+1)*((n : ℝ)+1+1)/g := hq.2
            _ ≤ Q*((n : ℝ)+2)^2/g := div_le_div_of_nonneg_right
              (by convert mul_le_mul_of_nonneg_left hpoly hQ.le using 1 <;> ring) hgR.le
            _ = _ := by ring
        rw [abs_mul,abs_sub_comm,abs_of_nonneg hq.1]
        have he := mul_le_mul_of_nonneg_left hbig (abs_nonneg (canonicalDilatonCoefficient Y (n+1)))
        convert he using 1 <;> ring
      _ = (Q/(g : ℝ))*(∑ n ∈ Finset.range N, ((n : ℝ)+2)^2*|canonicalDilatonCoefficient Y (n+1)|) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (Q/(g : ℝ))*M := mul_le_mul_of_nonneg_left (hmoment Y hY N) (div_nonneg hQ.le hgR.le)
      _ = _ := by ring
  have hsum := (canonicalDilatonCoefficient_succ_hasSum Y).tendsto_sum_nat
  have ht : Tendsto (fun N : ℕ => |R-(∑ n ∈ Finset.range N, canonicalDilatonCoefficient Y (n+1))|)
      atTop (nhds |R-A Y|) := (tendsto_const_nhds.sub hsum).abs
  exact le_of_tendsto ht (eventually_atTop.mpr ⟨dimension g (p+1),fun N hN => herror N hN⟩)
lemma marked_cusp_all_from_quadratic (P : PsiTheory)
    (hall : ∀ q : ℕ, 1≤q → ∃ Q : ℝ, 0<Q ∧ ∀ g : ℕ, 1≤g → ∀ d : List ℕ, d.length=q →
      ∀ Y ∈ Icc (0:ℝ) y₀, 0≤1-profile P g d Y ∧ 1-profile P g d Y≤Q*(d.sum : ℝ)*(d.sum+1)/g)
    (p : ℕ) : ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |(complexity g p : ℝ)*W P g p Y/W P g (p+1) Y-A Y|≤C/g := by
  obtain ⟨Q,hQ,hquad⟩ := hall (p+1) (by omega)
  obtain ⟨C,hC,hbound⟩ := cusp_estimate_of_quadratic P p Q hQ hquad
  refine ⟨C,hC,2,?_⟩
  intro g hg Y hY
  exact hbound g (by omega) (by unfold Stable; omega) Y hY
end WP
