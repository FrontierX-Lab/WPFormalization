import WPFormalization.Critical.CutBoundaryEnvelope
import WPFormalization.External.CriticalVolumeBounds

/-! Uniform product-volume ratios for actual component genera and cusp allocations. The only new deferred roots are the separately licensed classical Shen--Wu volume bounds. -/

noncomputable section
namespace WP.Critical
open Finset

lemma cut_gamma_ratio_algebra (Q h:ℕ) (hQ:1≤Q) (d:Fin Q→ℕ)
    (hd:∀i,1≤d i) (hsum:(∑i,d i)=h)
    (V:Fin Q→ℝ) (V₀ C c B:ℝ) (hV:∀i,0≤V i)
    (hC:0<C) (hc:0<c) (hB:1≤B)
    (hupper:∀i,V i≤C*B^(d i-1)*Real.Gamma (d i)/Real.sqrt (d i))
    (hlower:c*B^(h-1)*Real.Gamma h/Real.sqrt h≤V₀) :
    (∏i,V i)/V₀≤(C^Q/c)*(Q:ℝ)*(∏i,Real.Gamma (d i))/Real.Gamma h := by
  have hQle : Q≤h := by
    have he := sum_le_sum (fun i (_:i∈univ)=>hd i)
    simpa only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one,hsum] using he
  have hh : 0<h := by omega
  have hp : 0<(h:ℝ) := by exact_mod_cast hh
  have hBpos : 0<B := zero_lt_one.trans_le hB
  have hΓ : 0<Real.Gamma (h:ℝ) := Real.Gamma_pos_of_pos hp
  have hS : 0<(∏i:Fin Q,Real.sqrt (d i)) := prod_pos (fun i _=>
    Real.sqrt_pos.mpr (by exact_mod_cast (by have:=hd i;omega:0<d i)))
  have hP : 0<(∏i:Fin Q,Real.Gamma (d i)) := prod_pos (fun i _=>
    Real.Gamma_pos_of_pos (by exact_mod_cast (by have:=hd i;omega:0<d i)))
  have hpower : (∏i:Fin Q,B^(d i-1))≤B^(h-1) := by
    rw [prod_pow_eq_pow_sum]
    apply pow_le_pow_right₀ hB
    have he (i:Fin Q) : (d i-1)+1=d i := by have:=hd i;omega
    have hs := congrArg (fun f:Fin Q→ℕ=>∑i,f i) (funext he)
    simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hs
    rw [hsum] at hs
    omega
  have hu : (∏i:Fin Q,V i)≤
      C^Q*B^(h-1)*(∏i:Fin Q,Real.Gamma (d i))/(∏i:Fin Q,Real.sqrt (d i)) := by
    have he := prod_le_prod₀ (fun i (_:i∈univ)=>hV i) (fun i (_:i∈univ)=>hupper i)
    simp only [prod_div_distrib,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin] at he
    refine he.trans ?_
    apply div_le_div_of_nonneg_right _ hS.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower (by positivity)) hP.le
  have hL : 0<c*B^(h-1)*Real.Gamma h/Real.sqrt h := by positivity
  have hv : 0<V₀ := hL.trans_le hlower
  have hsqrt : Real.sqrt (h:ℝ)/(∏i:Fin Q,Real.sqrt (d i))≤(Q:ℝ) := by
    apply (div_le_iff₀ hS).mpr
    have he := cut_sqrt_budget (fun i:Fin Q=>(d i:ℝ))
      (fun i=>by exact_mod_cast hd i)
    rw [←Nat.cast_sum,hsum] at he
    simpa only [Fintype.card_fin] using he
  calc
    _ ≤ (C^Q*B^(h-1)*(∏i:Fin Q,Real.Gamma (d i))/(∏i:Fin Q,Real.sqrt (d i)))/V₀ :=
      div_le_div_of_nonneg_right hu hv.le
    _ ≤ (C^Q*B^(h-1)*(∏i:Fin Q,Real.Gamma (d i))/(∏i:Fin Q,Real.sqrt (d i)))/
        (c*B^(h-1)*Real.Gamma h/Real.sqrt h) :=
      div_le_div_of_nonneg_left (by positivity) hL hlower
    _ = (C^Q/c)*(Real.sqrt h/(∏i:Fin Q,Real.sqrt (d i)))*
        ((∏i:Fin Q,Real.Gamma (d i))/Real.Gamma h) := by field_simp
    _ ≤ (C^Q/c)*(Q:ℝ)*((∏i:Fin Q,Real.Gamma (d i))/Real.Gamma h) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt (by positivity))
        (div_pos hP hΓ).le
    _ = _ := by ring

end WP.Critical
namespace WP.Critical

/-- The actual WP-model product-volume ratio, with constants uniform over all
component genera and cusp allocations of the fixed graph size. -/
lemma cut_volume_gamma_ratio (P:PsiTheory) (Q:ℕ) (hQ:1≤Q) (A:ℝ) (hA:0<A) :
    ∃K:ℝ,0<K ∧ ∃G:ℕ,∀g≥G,∀n:ℕ,(n:ℝ)≤A*Real.sqrt g →
      ∀a b:Fin Q→ℕ,(∀i,1≤b i) → (∀i,Stable (a i) (b i)) →
      (∑i:Fin Q,complexity (a i) (b i))=complexity g n →
      (∏i:Fin Q,volumeModel P (a i) (b i))/volumeModel P g n ≤
        K*(∏i:Fin Q,Real.Gamma (complexity (a i) (b i)))/Real.Gamma (complexity g n) := by
  obtain ⟨C,hC,hupper⟩ := WP.External.shenWu_volume_upper P
  obtain ⟨c,hc,G,hLower⟩ := WP.External.shenWu_volume_critical_lower P A hA
  have hQR : 0<(Q:ℝ) := by exact_mod_cast (by omega:0<Q)
  refine ⟨(C^Q/c)*(Q:ℝ),by positivity,max G 2,?_⟩
  intro g hg n hn a b hb hs hbudget
  have hB : (1:ℝ)≤4*Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hd (i:Fin Q) : 1≤complexity (a i) (b i) := by
    have hi:=hs i
    unfold Stable complexity at *
    omega
  exact cut_gamma_ratio_algebra Q (complexity g n) hQ (fun i=>complexity (a i) (b i))
    hd hbudget (fun i=>volumeModel P (a i) (b i)) (volumeModel P g n) C c (4*Real.pi^2)
    (fun i=>(cut_volumeModel_pos P _ _ (hb i) (hs i)).le) hC hc hB
    (fun i=>hupper (a i) (b i) (hs i)) (hLower g (by omega) n hn)

end WP.Critical
