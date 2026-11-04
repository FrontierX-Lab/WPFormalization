import WPFormalization.Marked.GrowingProfile
import WPFormalization.Marked.CuspFromProfile
import WPFormalization.Statements.Coefficients

/-! The true dilaton identity at the current genus transports the uniform all-degree profile bound to the original normalized cusp correction. The child complexity shift h+1 is retained. -/
noncomputable section
namespace WP
open Set Filter
lemma canonical_cusp_error_of_head_bound (P : PsiTheory) (g p : ℕ) (hs : Stable g p)
    (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) (E U : ℝ) (hE : 0 ≤ E)
    (hhead : ∀n:ℕ,|profile P g ((n+1)::List.replicate p 0) Y-1| ≤ E*((n:ℝ)+2)^2)
    (hmoment : ∀N:ℕ,(∑n∈Finset.range N,((n:ℝ)+2)^2*|canonicalDilatonCoefficient Y (n+1)|) ≤ U) :
    |(complexity g p:ℝ)*W P g p Y/W P g (p+1) Y-A Y| ≤ E*U := by
  let R := (complexity g p:ℝ)*W P g p Y/W P g (p+1) Y
  have herror (N : ℕ) (hN : dimension g (p+1) ≤ N) :
      |R-(∑n∈Finset.range N,canonicalDilatonCoefficient Y (n+1))| ≤ E*U := by
    have hext := canonical_profile_sum_extended_stable P g p N hs hN Y hY
    have heq : R-(∑n∈Finset.range N,canonicalDilatonCoefficient Y (n+1))=
        ∑n∈Finset.range N,canonicalDilatonCoefficient Y (n+1)*
          (profile P g ((n+1)::List.replicate p 0) Y-1) := by
      change R=∑n∈Finset.range N,canonicalDilatonCoefficient Y (n+1)*profile P g ((n+1)::List.replicate p 0) Y at hext
      rw [hext,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [heq]
    calc
      _ ≤ ∑n∈Finset.range N,|canonicalDilatonCoefficient Y (n+1)*
          (profile P g ((n+1)::List.replicate p 0) Y-1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑n∈Finset.range N,E*(((n:ℝ)+2)^2*|canonicalDilatonCoefficient Y (n+1)|) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [abs_mul]
        have he := mul_le_mul_of_nonneg_left (hhead n) (abs_nonneg (canonicalDilatonCoefficient Y (n+1)))
        convert he using 1 <;>ring
      _ = E*(∑n∈Finset.range N,((n:ℝ)+2)^2*|canonicalDilatonCoefficient Y (n+1)|) := by rw [Finset.mul_sum]
      _ ≤ E*U := mul_le_mul_of_nonneg_left (hmoment N) hE
  have hsum := (canonicalDilatonCoefficient_succ_hasSum Y).tendsto_sum_nat
  have ht : Tendsto (fun N:ℕ=>|R-(∑n∈Finset.range N,canonicalDilatonCoefficient Y (n+1))|)
      atTop (nhds |R-A Y|) := (tendsto_const_nhds.sub hsum).abs
  exact le_of_tendsto ht (eventually_atTop.mpr ⟨dimension g (p+1),fun N hN=>herror N hN⟩)
lemma growing_marking_cusp_first_order_proof (P : PsiTheory) (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ,0 < C ∧ ∃ H : ℕ,∀g p:ℕ,1 ≤ p → H ≤ complexity g p →
      (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) → ∀Y∈Icc (0:ℝ) y₀,
      |cuspCorrection P g p Y-1| ≤ C*((p:ℝ)+1)/(complexity g p:ℝ) := by
  obtain ⟨Q,hQ,H,hprofile⟩ := growing_marking_profile_first_order_proof P (M+1) (by positivity)
  obtain ⟨U,hU,hmoment⟩ := canonicalDilatonCoefficient_succ_quadratic_abs_sum_uniform
  obtain ⟨a₀,ha₀,hA⟩ := singleMarking_A_uniform_lower
  refine ⟨2*Q*U/a₀,by positivity,H+2,?_⟩
  intro g p hp hH hpM Y hY
  let h : ℝ := complexity g p
  have hh2 : (2:ℝ) ≤ h := by dsimp [h];exact_mod_cast (show 2 ≤ complexity g p by omega)
  have hh : 0 < h := by linarith
  have hs : Stable g p := by unfold Stable complexity at *;omega
  have hc : complexity g (p+1)=complexity g p+1 := by unfold complexity;unfold Stable at hs;omega
  have hcR : (complexity g (p+1):ℝ)=h+1 := by rw [hc,Nat.cast_add,Nat.cast_one]
  have hroot : 1 ≤ Real.sqrt (complexity g (p+1):ℝ) := Real.one_le_sqrt.mpr (by rw [hcR];linarith)
  have hrootle : Real.sqrt h ≤ Real.sqrt (complexity g (p+1):ℝ) := Real.sqrt_le_sqrt (by rw [hcR];linarith)
  have hpchild : ((p+1:ℕ):ℝ) ≤ (M+1)*Real.sqrt (complexity g (p+1):ℝ) := by
    rw [Nat.cast_add,Nat.cast_one]
    have he := mul_le_mul_of_nonneg_left hrootle hM.le
    nlinarith only [hpM,he,hroot]
  let E : ℝ := Q*((p:ℝ)+3)/h
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hhead (n : ℕ) : |profile P g ((n+1)::List.replicate p 0) Y-1| ≤ E*((n:ℝ)+2)^2 := by
    have hq := hprofile g (p+1) (by omega) (by omega) hpchild Y hY
      ((n+1)::List.replicate p 0) (by simp)
    have hb := hq.2.trans (min_le_right 1 _)
    simp only [List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,Nat.cast_add,Nat.cast_one] at hb
    have hpoly : ((n:ℝ)+1)*((n:ℝ)+1+(p+1)+1) ≤ ((p:ℝ)+3)*((n:ℝ)+2)^2 := by
      have hpn : 0 ≤ ((p:ℝ)+2)*(n:ℝ)^2 := by positivity
      have hnn : 0 ≤ (3*(p:ℝ)+8)*(n:ℝ) := by positivity
      nlinarith only [hpn,hnn,Nat.cast_nonneg (α:=ℝ) p]
    rw [abs_sub_comm,abs_of_nonneg hq.1]
    calc
      _ ≤ Q*((n:ℝ)+1)*((n:ℝ)+1+(p+1)+1)/(complexity g (p+1):ℝ) := hb
      _ ≤ Q*(((p:ℝ)+3)*((n:ℝ)+2)^2)/(complexity g (p+1):ℝ) :=
        div_le_div_of_nonneg_right (by convert mul_le_mul_of_nonneg_left hpoly hQ.le using 1 <;>ring) (by positivity)
      _ ≤ Q*(((p:ℝ)+3)*((n:ℝ)+2)^2)/h :=
        div_le_div_of_nonneg_left (by positivity) hh (by rw [hcR];linarith)
      _ = _ := by dsimp [E];ring
  have hraw := canonical_cusp_error_of_head_bound P g p hs Y hY E U hE hhead (hmoment Y hY)
  have haY : 0 < A Y := ha₀.trans_le (hA Y hY)
  have hW : 0 < W P g (p+1) Y := W_pos P g (p+1) (by omega) (by unfold Stable at hs ⊢;omega) Y hY
  have hid : cuspCorrection P g p Y-1=
      ((complexity g p:ℝ)*W P g p Y/W P g (p+1) Y-A Y)/A Y := by
    unfold cuspCorrection
    field_simp [haY.ne',hW.ne']
  rw [hid,abs_div,abs_of_pos haY]
  calc
    _ ≤ (E*U)/A Y := div_le_div_of_nonneg_right hraw haY.le
    _ ≤ (E*U)/a₀ := div_le_div_of_nonneg_left (by positivity) ha₀ (hA Y hY)
    _ = (Q*U/a₀)*((p:ℝ)+3)/h := by dsimp [E];ring
    _ ≤ (2*Q*U/a₀)*((p:ℝ)+1)/h := by
      apply div_le_div_of_nonneg_right _ hh.le
      have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
      have he := mul_le_mul_of_nonneg_left (show (p:ℝ)+3 ≤ 2*((p:ℝ)+1) by linarith) (show 0 ≤ Q*U/a₀ by positivity)
      convert he using 1 <;>ring
end WP
