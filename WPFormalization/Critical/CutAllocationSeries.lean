import WPFormalization.Critical.CutGammaConvolution
import WPFormalization.Critical.CutCuspSeries
import WPFormalization.Critical.CutNumerical

/-! Exact stable Gamma cusp-allocation generating series, their complete ordered allocation sum, and the original genus-scale numerical estimates. This is the numerical allocation sum; geometric orbit counting is handled separately. -/

noncomputable section
namespace WP.Critical
open Finset

/-- The exact cusp-allocation series Gamma(h)*(1-z)^(-h) at a stable vertex. -/
def cutStableCuspSeries (h : ℕ) : PowerSeries ℝ :=
  PowerSeries.C (Real.Gamma h)*(PowerSeries.invOneSubPow ℝ h).val

lemma cutStableCuspSeries_coeff_gamma (h q : ℕ) (hh : 1 ≤ h) :
    PowerSeries.coeff q (cutStableCuspSeries h)=
      Real.Gamma ((h:ℝ)+(q:ℝ))/(q.factorial:ℝ) := by
  obtain ⟨s,rfl⟩ : ∃s:ℕ,h=s+1 := ⟨h-1,by omega⟩
  rw [cutStableCuspSeries,PowerSeries.coeff_C_mul,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,PowerSeries.coeff_mk,
    Nat.cast_add,Nat.cast_one,Real.Gamma_nat_eq_factorial]
  rw [show (s:ℝ)+1+(q:ℝ)=((s+q:ℕ):ℝ)+1 by push_cast;ring,
    Real.Gamma_nat_eq_factorial]
  have hqf : (q.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero q
  apply (eq_div_iff hqf).mpr
  have he := Nat.choose_mul_factorial_mul_factorial (show s ≤ s+q by omega)
  rw [show s+q-s=q by omega] at he
  exact_mod_cast (by nlinarith only [he] : s.factorial*(s+q).choose s*q.factorial=(s+q).factorial)

lemma cutStableCuspSeries_prod (w : ℕ) (h : ℕ→ℕ) :
    (∏i∈range w,cutStableCuspSeries (h i)) =
      PowerSeries.C (∏i∈range w,Real.Gamma (h i)) *
        (PowerSeries.invOneSubPow ℝ (∑i∈range w,h i)).val := by
  induction w with
  | zero => simp [PowerSeries.invOneSubPow_zero]
  | succ w ih =>
    rw [prod_range_succ,sum_range_succ,ih,cutStableCuspSeries,
      PowerSeries.invOneSubPow_add,Units.val_mul,prod_range_succ,map_mul]
    ring

/-- Stable positive complexities are enumerated without parity restrictions.
An index l contributes h_i=l_i+1, so its total complexity is N+w. -/
def cutStableAllocationSeries (w N : ℕ) : PowerSeries ℝ :=
  ∑l∈finsuppAntidiag (range w) N,
    ∏i∈range w,cutStableCuspSeries (l i+1)

lemma cutStableAllocationSeries_factor (w N : ℕ) :
    cutStableAllocationSeries w N =
      PowerSeries.C (cutStableConvolution w N) *
        (PowerSeries.invOneSubPow ℝ (N+w)).val := by
  unfold cutStableAllocationSeries
  have he (l:ℕ→₀ℕ) (hl:l∈finsuppAntidiag (range w) N) :
      (∑i∈range w,(l i+1))=N+w := by
    have hs := (mem_finsuppAntidiag.mp hl).1
    simp only [sum_add_distrib,sum_const,card_range,smul_eq_mul,mul_one]
    exact congrArg (fun t=>t+w) hs
  simp_rw [cutStableCuspSeries_prod]
  calc
    _ = ∑l∈finsuppAntidiag (range w) N,
        PowerSeries.C (∏i∈range w,Real.Gamma ((l i:ℝ)+1)) *
          (PowerSeries.invOneSubPow ℝ (N+w)).val := by
      apply sum_congr rfl
      intro l hl
      rw [he l hl]
      simp only [Nat.cast_add,Nat.cast_one]
    _ = _ := by
      rw [←sum_mul,←map_sum,cutStableConvolution_eq_coeff,PowerSeries.coeff_pow]
      simp only [Real.Gamma_nat_eq_factorial,cutFactorialSeries,PowerSeries.coeff_mk]

end WP.Critical

namespace WP.Critical
open Finset

lemma cutInvOneSubPow_coeff_gamma (H q : ℕ) (hH : 1 ≤ H) :
    PowerSeries.coeff q (PowerSeries.invOneSubPow ℝ H).val =
      Real.Gamma ((H:ℝ)+(q:ℝ))/(Real.Gamma H*(q.factorial:ℝ)) := by
  have hg : Real.Gamma (H:ℝ)≠0 :=
    (Real.Gamma_pos_of_pos (by exact_mod_cast (by omega:0<H))).ne'
  have hf : (q.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero q
  have he := cutStableCuspSeries_coeff_gamma H q hH
  rw [cutStableCuspSeries,PowerSeries.coeff_C_mul] at he
  apply (eq_div_iff (mul_ne_zero hg hf)).mpr
  calc
    _ = (Real.Gamma (H:ℝ)*PowerSeries.coeff q (PowerSeries.invOneSubPow ℝ H).val)*q.factorial := by ring
    _ = _ := by rw [he];exact div_mul_cancel₀ _ hf

/-- Exact coefficient extraction, keeping the cusp multinomial falling
factorial and both Gamma normalizations. -/
lemma cutAllocation_coeff_identity (f : PowerSeries ℝ) (u w N n h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (hdegree : N+w+n=h+u) :
    ((n.factorial:ℝ)/Real.Gamma h)*
        PowerSeries.coeff n (f*cutStableAllocationSeries w N) =
      (cutStableConvolution w N/Real.Gamma (N+w)) * cutGammaWeightedSum f u n h := by
  have hH : 1 ≤ N+w := by omega
  have hg : Real.Gamma (h:ℝ)≠0 :=
    (Real.Gamma_pos_of_pos (by exact_mod_cast (by omega:0<h))).ne'
  have hGH : Real.Gamma ((N+w:ℕ):ℝ)≠0 :=
    (Real.Gamma_pos_of_pos (by exact_mod_cast (by omega:0<N+w))).ne'
  have he : f*cutStableAllocationSeries w N=
      PowerSeries.C (cutStableConvolution w N)*
        (f*(PowerSeries.invOneSubPow ℝ (N+w)).val) := by
    rw [cutStableAllocationSeries_factor]
    ring
  rw [he,PowerSeries.coeff_C_mul,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,cutGammaWeightedSum]
  simp only [mul_sum]
  apply sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by have:=mem_range.mp hm;omega
  rw [cutInvOneSubPow_coeff_gamma (N+w) (n-m) hH]
  have hcast : ((N+w:ℕ):ℝ)+((n-m:ℕ):ℝ)=(h:ℝ)+(u:ℝ)-(m:ℝ) := by
    have hc : ((N+w+n:ℕ):ℝ)=((h+u:ℕ):ℝ) := congrArg Nat.cast hdegree
    push_cast at hc
    rw [Nat.cast_sub hmn]
    push_cast
    linarith
  rw [hcast]
  have hfac : (n.factorial:ℝ)=((n-m).factorial:ℝ)*(n.descFactorial m:ℝ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hmn).symm
  have hf : ((n-m).factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (n-m)
  rw [hfac]
  push_cast at hGH ⊢
  field_simp
  <;>ring

/-- The genuine coefficient allocation is bounded by the reduced sum after
summing every stable complexity and dropping genus parity restrictions. -/
lemma cutAllocation_coeff_upper (f : PowerSeries ℝ) (u w N n h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (hdegree : N+w+n=h+u)
    (hf : ∀m,0 ≤ PowerSeries.coeff m f) (hn : 2*(n:ℝ) ≤ h) :
    ((n.factorial:ℝ)/Real.Gamma h)*
        PowerSeries.coeff n (f*cutStableAllocationSeries w N)  ≤
      (3:ℝ)^w*cutCriticalReducedSum f u w n h := by
  rw [cutAllocation_coeff_identity f u w N n h hw hh hdegree]
  have hp : 0<(h:ℝ) := by exact_mod_cast (by omega:0<h)
  have hHpos : 0<((N+w:ℕ):ℝ) := by exact_mod_cast (by omega:0<N+w)
  have hsum := cutGammaWeightedSum_nonneg f u n h hf hp hn
  have hb := div_le_div_of_nonneg_right (cutStableConvolution_bound w N)
    (Real.Gamma_pos_of_pos hHpos).le
  rw [←Real.Gamma_nat_eq_factorial] at hb
  have hc : (h:ℝ)-(n:ℝ)+(u:ℝ)=((N+w:ℕ):ℝ) := by
    have he : ((N+w+n:ℕ):ℝ)=((h+u:ℕ):ℝ) := congrArg Nat.cast hdegree
    push_cast at he ⊢
    linarith
  have ha : (h:ℝ)-(n:ℝ)+(u:ℝ)-(w:ℝ)+1=(N:ℝ)+1 := by
    rw [hc]
    push_cast
    ring
  unfold cutCriticalReducedSum
  rw [ha,hc]
  push_cast at hb ⊢
  convert mul_le_mul_of_nonneg_right hb hsum using 1 <;>ring

end WP.Critical
namespace WP.Critical

lemma cutAllocation_coeff_rate_of_reduced (f : PowerSeries ℝ) (u w : ℕ)
    (hw : 1≤w) (A : ℝ) (hA : 0<A) (δ : ℝ)
    (hf : ∀m,0≤PowerSeries.coeff m f)
    (hreduced : ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n:ℕ,H₀≤h → (n:ℝ)≤A*Real.sqrt h →
      cutCriticalReducedSum f u w n h≤C*(h:ℝ)^δ) :
    ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n N:ℕ,H₀≤h → (n:ℝ)≤A*Real.sqrt h →
      N+w+n=h+u →
      ((n.factorial:ℝ)/Real.Gamma h)*
        PowerSeries.coeff n (f*cutStableAllocationSeries w N) ≤ C*(h:ℝ)^δ := by
  obtain ⟨C,hC,H₁,hbound⟩ := hreduced
  obtain ⟨H₂,hH₂⟩ := exists_nat_ge (1+4*A^2)
  refine ⟨(3:ℝ)^w*C,by positivity,max H₁ H₂,?_⟩
  intro h n N hh hn hdegree
  have hH : (H₂:ℝ)≤h := by exact_mod_cast (show H₂≤h by omega)
  have hp : 0<(h:ℝ) := by nlinarith [sq_nonneg A]
  have hsq : (n:ℝ)^2≤A^2*(h:ℝ) := by
    have hs := (sq_le_sq₀ (Nat.cast_nonneg n) (by positivity:0≤A*Real.sqrt h)).mpr hn
    simpa only [mul_pow,Real.sq_sqrt hp.le] using hs
  have hhalf : 2*(n:ℝ)≤h := by nlinarith [sq_nonneg ((h:ℝ)-2*n)]
  have hhn : 1≤h := by exact_mod_cast (show 0<(h:ℝ) from hp)
  have hb := cutAllocation_coeff_upper f u w N n h hw hhn hdegree hf hhalf
  exact hb.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound h n (by omega) hn) (by positivity:0≤(3:ℝ)^w))

/-- The full ordered stable-complexity and cusp-allocation sum has the original
critical exponent. No free coefficient sequence occurs in this statement. -/
lemma cutCuspAllocationSum_rate (u v w : ℕ) (hw : 1≤w) (A : ℝ) (hA : 0<A) :
    ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n N:ℕ,H₀≤h → (n:ℝ)≤A*Real.sqrt h →
      N+w+n=h+u →
      ((n.factorial:ℝ)/Real.Gamma h)*
        PowerSeries.coeff n (cutCuspAllocationSeries u v*cutStableAllocationSeries w N) ≤
          C*(h:ℝ)^(1-(w:ℝ)-(v:ℝ)/2) :=
  cutAllocation_coeff_rate_of_reduced _ u w hw A hA _
    (cutCuspAllocation_coeff_nonneg u v) (cutCriticalReducedSum_rate u v w hw A hA)

lemma cutMarkedCuspAllocationSum_rate (u v w : ℕ) (hu : 1≤u) (hw : 1≤w)
    (A : ℝ) (hA : 0<A) :
    ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n N:ℕ,H₀≤h → (n:ℝ)≤A*Real.sqrt h →
      N+w+n=h+u →
      ((n.factorial:ℝ)/Real.Gamma h)*
        PowerSeries.coeff n (cutMarkedCuspAllocationSeries u v*cutStableAllocationSeries w N) ≤
          C*(h:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2) :=
  cutAllocation_coeff_rate_of_reduced _ u w hw A hA _
    (cutMarkedCuspAllocation_coeff_nonneg u v) (cutCriticalMarkedReducedSum_rate u v w hu hw A hA)

end WP.Critical
namespace WP.Critical

lemma cutAllocation_coeff_genus_rate_of_rate (f : PowerSeries ℝ) (u w : ℕ)
    (A : ℝ) (hA : 0<A) (δ : ℝ) (hδ : δ ≤ 0)
    (hrate : ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n N:ℕ,H₀ ≤ h → (n:ℝ) ≤ A*Real.sqrt h →
      N+w+n=h+u →
      ((n.factorial:ℝ)/Real.Gamma h)*
        PowerSeries.coeff n (f*cutStableAllocationSeries w N) ≤ C*(h:ℝ)^δ) :
    ∃C:ℝ,0<C ∧ ∃G:ℕ,∀g≥G,∀n:ℕ,(n:ℝ) ≤ A*Real.sqrt g →
      ((n.factorial:ℝ)/Real.Gamma ((2*g+n-2:ℕ):ℝ))*
        PowerSeries.coeff n (f*cutStableAllocationSeries w (2*g-2+u-w)) ≤ C*(g:ℝ)^δ := by
  obtain ⟨C,hC,H₀,hbound⟩ := hrate
  refine ⟨C,hC,max H₀ (w+2),?_⟩
  intro g hg n hn
  have hgg : g ≤ 2*g+n-2 := by omega
  have hp : 0<(g:ℝ) := by exact_mod_cast (by omega:0<g)
  have hggR : (g:ℝ) ≤ ((2*g+n-2:ℕ):ℝ) := by exact_mod_cast hgg
  have hn' : (n:ℝ) ≤ A*Real.sqrt ((2*g+n-2:ℕ):ℝ) :=
    hn.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hggR) hA.le)
  have hb := hbound (2*g+n-2) n (2*g-2+u-w) (by omega) hn' (by omega)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hp hggR hδ) hC.le)

lemma cutCuspAllocationSum_genus_rate (u v w : ℕ) (hw : 1 ≤ w) (A : ℝ) (hA : 0<A) :
    ∃C:ℝ,0<C ∧ ∃G:ℕ,∀g≥G,∀n:ℕ,(n:ℝ) ≤ A*Real.sqrt g →
      ((n.factorial:ℝ)/Real.Gamma ((2*g+n-2:ℕ):ℝ))*
        PowerSeries.coeff n (cutCuspAllocationSeries u v*
          cutStableAllocationSeries w (2*g-2+u-w))  ≤  C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2) := by
  apply cutAllocation_coeff_genus_rate_of_rate _ u w A hA
    (1-(w:ℝ)-(v:ℝ)/2) _ (cutCuspAllocationSum_rate u v w hw A hA)
  have hwR : (1:ℝ) ≤ w := by exact_mod_cast hw
  linarith [Nat.cast_nonneg (α:=ℝ) v]

lemma cutMarkedCuspAllocationSum_genus_rate (u v w : ℕ) (hu : 1 ≤ u) (hw : 1 ≤ w)
    (A : ℝ) (hA : 0<A) :
    ∃C:ℝ,0<C ∧ ∃G:ℕ,∀g≥G,∀n:ℕ,(n:ℝ) ≤ A*Real.sqrt g →
      ((n.factorial:ℝ)/Real.Gamma ((2*g+n-2:ℕ):ℝ))*
        PowerSeries.coeff n (cutMarkedCuspAllocationSeries u v*
          cutStableAllocationSeries w (2*g-2+u-w))  ≤
            C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2) := by
  apply cutAllocation_coeff_genus_rate_of_rate _ u w A hA
    (1-(w:ℝ)-((v:ℝ)+1)/2) _ (cutMarkedCuspAllocationSum_rate u v w hu hw A hA)
  have hwR : (1:ℝ) ≤ w := by exact_mod_cast hw
  linarith [Nat.cast_nonneg (α:=ℝ) v]

end WP.Critical
