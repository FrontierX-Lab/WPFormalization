import WPFormalization.Critical.CutAllocationSeries

/-! Actual stable genus assignments inject into the complete positive-complexity allocation sum. All Gamma weights are retained while only parity restrictions are dropped. -/
noncomputable section

namespace WP.Critical
open Finset

/-- The same complete stable allocation indexed by the actual finite vertex
set, for direct comparison with graph genus assignments. -/
def cutStableAllocationSeriesFin (w N:ℕ) : PowerSeries ℝ :=
  ∑l∈finsuppAntidiag (univ:Finset (Fin w)) N,
    ∏i:Fin w,cutStableCuspSeries (l i+1)

lemma cutStableConvolution_eq_fin_sum (w N:ℕ) :
    cutStableConvolution w N=
      ∑l∈finsuppAntidiag (univ:Finset (Fin w)) N,∏i:Fin w,((l i).factorial:ℝ) := by
  rw [cutStableConvolution_eq_coeff]
  have he : cutFactorialSeries^w=∏_i:Fin w,cutFactorialSeries := by simp
  rw [he,PowerSeries.coeff_prod]
  simp only [cutFactorialSeries,PowerSeries.coeff_mk]

lemma cutStableCuspSeries_fin_prod {w:ℕ} (h:Fin w→ℕ) :
    (∏i:Fin w,cutStableCuspSeries (h i))=
      PowerSeries.C (∏i:Fin w,Real.Gamma (h i))*
        (PowerSeries.invOneSubPow ℝ (∑i:Fin w,h i)).val := by
  induction w with
  | zero => simp [PowerSeries.invOneSubPow_zero]
  | succ w ih =>
    rw [Fin.prod_univ_succ,Fin.sum_univ_succ,ih (fun i=>h i.succ),cutStableCuspSeries,
      PowerSeries.invOneSubPow_add,Units.val_mul,Fin.prod_univ_succ,map_mul]
    ring

lemma cutStableAllocationSeriesFin_factor (w N:ℕ) :
    cutStableAllocationSeriesFin w N=
      PowerSeries.C (cutStableConvolution w N)*(PowerSeries.invOneSubPow ℝ (N+w)).val := by
  unfold cutStableAllocationSeriesFin
  have he (l:Fin w→₀ℕ) (hl:l∈finsuppAntidiag univ N) : (∑i:Fin w,(l i+1))=N+w := by
    have hs := (mem_finsuppAntidiag.mp hl).1
    simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
    exact congrArg (fun t=>t+w) hs
  simp_rw [cutStableCuspSeries_fin_prod]
  calc
    _ = ∑l∈finsuppAntidiag (univ:Finset (Fin w)) N,
        PowerSeries.C (∏i:Fin w,Real.Gamma ((l i:ℝ)+1)) *
          (PowerSeries.invOneSubPow ℝ (N+w)).val := by
      apply sum_congr rfl
      intro l hl
      rw [he l hl]
      simp only [Nat.cast_add,Nat.cast_one]
    _ = _ := by
      rw [←sum_mul,←map_sum,cutStableConvolution_eq_fin_sum]
      simp only [Real.Gamma_nat_eq_factorial]

lemma cutStableAllocationSeriesFin_eq (w N:ℕ) :
    cutStableAllocationSeriesFin w N=cutStableAllocationSeries w N := by
  rw [cutStableAllocationSeriesFin_factor,cutStableAllocationSeries_factor]

lemma cutStableCuspSeries_coeff_nonneg (h:ℕ) (hh:1≤h) :
    ∀q,0≤PowerSeries.coeff q (cutStableCuspSeries h) := by
  intro q
  rw [cutStableCuspSeries_coeff_gamma h q hh]
  apply div_nonneg
  · apply (Real.Gamma_pos_of_pos _).le
    have hnat : 0<h+q := by omega
    exact_mod_cast hnat
  · positivity

lemma cutSeries_prod_nonneg {ι:Type*} [Fintype ι] (f:ι→PowerSeries ℝ)
    (hf:∀i m,0≤PowerSeries.coeff m (f i)) :
    ∀m,0≤PowerSeries.coeff m (∏i,f i) := by
  intro m
  classical
  rw [PowerSeries.coeff_prod]
  exact sum_nonneg (fun l _=>prod_nonneg (fun i _=>hf i _))

/-- The actual stable genus-to-complexity allocation, before dropping parity. -/
def cutStableGenusAllocation {w:ℕ} (p a:Fin w→ℕ) : Fin w→₀ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i=>complexity (a i) (p i)-1)

lemma cutStableGenusAllocation_apply {w:ℕ} (p a:Fin w→ℕ) (i:Fin w) :
    cutStableGenusAllocation p a i=complexity (a i) (p i)-1 := by
  exact congrFun ((Finsupp.equivFunOnFinite : (Fin w→₀ℕ) ≃ (Fin w→ℕ)).apply_symm_apply
    (fun j=>complexity (a j) (p j)-1)) i

lemma cutStableGenusAllocation_inj {w:ℕ} (p:Fin w→ℕ) (a b:Fin w→ℕ)
    (ha:∀i,Stable (a i) (p i)) (hb:∀i,Stable (b i) (p i))
    (he:cutStableGenusAllocation p a=cutStableGenusAllocation p b) : a=b := by
  funext i
  have h := congrArg (fun l:Fin w→₀ℕ=>l i) he
  simp only [cutStableGenusAllocation_apply] at h
  have ha' := ha i
  have hb' := hb i
  unfold Stable complexity at *
  omega

lemma cutStableGenusAllocation_mem {w N:ℕ} (p a:Fin w→ℕ)
    (ha:∀i,Stable (a i) (p i)) (hs:(∑i:Fin w,complexity (a i) (p i))=N+w) :
    cutStableGenusAllocation p a∈finsuppAntidiag univ N := by
  apply mem_finsuppAntidiag.mpr
  refine ⟨?_,subset_univ _⟩
  simp only [cutStableGenusAllocation_apply]
  have he (i:Fin w) : (complexity (a i) (p i)-1)+1=complexity (a i) (p i) := by
    have hi:=ha i
    unfold Stable complexity at *
    omega
  have hb := congrArg (fun f:Fin w→ℕ=>∑i,f i) (funext he)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hb
  omega

end WP.Critical

namespace WP.Critical
open Finset

/-- Dropping the stable genus parity constraints genuinely enlarges the full
coefficient sum: the genus assignment maps injectively into the complete
positive-complexity allocation, with its exact original Gamma weights. -/
lemma cutStableGenus_coefficient_majorant {w N:ℕ} (n:ℕ) (p:Fin w→ℕ)
    (s:Finset (Fin w→ℕ))
    (hs:∀a∈s,(∀i,Stable (a i) (p i)) ∧ (∑i:Fin w,complexity (a i) (p i))=N+w)
    (f:PowerSeries ℝ) (hf:∀m,0≤PowerSeries.coeff m f) :
    (∑a∈s,PowerSeries.coeff n
      (f*(∏i:Fin w,cutStableCuspSeries (complexity (a i) (p i))))) ≤
      PowerSeries.coeff n (f*cutStableAllocationSeries w N) := by
  classical
  let weight : (Fin w→₀ℕ)→ℝ := fun l=>
    PowerSeries.coeff n (f*(∏i:Fin w,cutStableCuspSeries (l i+1)))
  have hinj : Set.InjOn (cutStableGenusAllocation p) s := by
    intro a ha b hb he
    exact cutStableGenusAllocation_inj p a b (hs a ha).1 (hs b hb).1 he
  have hsub : s.image (cutStableGenusAllocation p)⊆finsuppAntidiag univ N := by
    intro l hl
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hl
    exact cutStableGenusAllocation_mem p a (hs a ha).1 (hs a ha).2
  have hnonneg (l:Fin w→₀ℕ) : 0≤weight l :=
    cutSeries_mul_nonneg f _ hf
      (cutSeries_prod_nonneg _ (fun i=>cutStableCuspSeries_coeff_nonneg (l i+1) (by omega))) n
  calc
    _ = ∑a∈s,weight (cutStableGenusAllocation p a) := by
      apply sum_congr rfl
      intro a ha
      dsimp only [weight]
      congr 2
      apply prod_congr rfl
      intro i hi
      rw [cutStableGenusAllocation_apply]
      have hstable := (hs a ha).1 i
      have hp : 1≤complexity (a i) (p i) := by unfold Stable complexity at *;omega
      rw [Nat.sub_add_cancel hp]
    _ = ∑l∈s.image (cutStableGenusAllocation p),weight l := (sum_image hinj).symm
    _ ≤ ∑l∈finsuppAntidiag univ N,weight l :=
      sum_le_sum_of_subset_of_nonneg hsub (fun l _ _=>hnonneg l)
    _ = _ := by
      rw [←cutStableAllocationSeriesFin_eq,cutStableAllocationSeriesFin,mul_sum,map_sum]

end WP.Critical
