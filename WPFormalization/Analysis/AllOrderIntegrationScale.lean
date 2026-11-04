import WPFormalization.Analysis.SecondLogScaleIntegration
noncomputable section
namespace WP.Analysis
open Set
lemma order_add_two_fifth_geometric (L : ℕ) :
    ((L:ℝ)+2)^5 ≤ 32*(32:ℝ)^L := by
  have hn : L+2 ≤ 2^(L+1) := by have ht : L+1 < 2^(L+1) := Nat.lt_two_pow_self;omega
  have hr : (L:ℝ)+2 ≤ (2:ℝ)^(L+1) := by exact_mod_cast hn
  calc _ ≤ ((2:ℝ)^(L+1))^5 := pow_le_pow_left₀ (by positivity) hr _
       _ = _ := by
         rw [←pow_mul,show (L+1)*5=5*(L+1) by omega,pow_mul,pow_succ]
         norm_num
         ring

lemma all_order_transport_log_scale_absorption (C B M h : ℝ) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hh : 1 ≤ h) (L : ℕ) :
    (C*B^(L+2)*((L+2).factorial:ℝ)^2/h^(L+1))*
      (M+(5/2:ℝ)*((L:ℝ)+1)*Real.log h) ≤
    (32*C*B^2*(M+3))*(32*B)^L*(L.factorial:ℝ)^2/h^L := by
  have hhp : 0 < h := by linarith
  have hL : 0 ≤ (L:ℝ) := Nat.cast_nonneg _
  have hlog : Real.log h ≤ h := (Real.log_le_sub_one_of_pos hhp).trans (by linarith)
  have hbr : (M+(5/2:ℝ)*((L:ℝ)+1)*Real.log h)/h ≤ M+3*((L:ℝ)+1) := by
    apply (div_le_iff₀ hhp).2
    have hm := mul_le_mul_of_nonneg_left hh hM
    have ht := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (5/2:ℝ)*((L:ℝ)+1))
    have hx : 0 ≤ ((L:ℝ)+1)*h := by positivity
    nlinarith
  have hp : (((L:ℝ)+1)*((L:ℝ)+2))^2 ≤ ((L:ℝ)+2)^4 := by
    calc _ ≤ (((L:ℝ)+2)*((L:ℝ)+2))^2 := by gcongr <;> linarith
         _ = _ := by ring
  have hb : M+3*((L:ℝ)+1) ≤ (M+3)*((L:ℝ)+2) := by nlinarith
  have hall : (((L:ℝ)+1)*((L:ℝ)+2))^2*((M+(5/2:ℝ)*((L:ℝ)+1)*Real.log h)/h) ≤
      32*(M+3)*(32:ℝ)^L := by
    calc _ ≤ (((L:ℝ)+1)*((L:ℝ)+2))^2*(M+3*((L:ℝ)+1)) := mul_le_mul_of_nonneg_left hbr (sq_nonneg _)
         _ ≤ ((L:ℝ)+2)^4*((M+3)*((L:ℝ)+2)) := mul_le_mul hp hb (by positivity) (by positivity)
         _ = (M+3)*((L:ℝ)+2)^5 := by ring
         _ ≤ (M+3)*(32*(32:ℝ)^L) := mul_le_mul_of_nonneg_left (order_add_two_fifth_geometric L) (by positivity)
         _ = _ := by ring
  have ht := mul_le_mul_of_nonneg_left hall (by positivity : 0 ≤ C*B^2*B^L*(L.factorial:ℝ)^2/h^L)
  convert ht using 1
  · rw [Nat.factorial_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    simp only [pow_succ]
    field_simp [hhp.ne']
    <;> ring
  · rw [mul_pow]
    ring

lemma all_order_log_scale_matching (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ h : ℝ, H ≤ h → ∀ L : ℕ, 1 ≤ L →
      let V := y₀-1/h^(L+1)
      V ∈ Ico (0:ℝ) y₀ ∧ y₀-V ≤ δ₀ := by
  let H : ℝ := 1+1/(min δ₀ y₀)
  have hm : 0 < min δ₀ y₀ := lt_min hδ₀ y₀_pos
  have hH : 1 ≤ H := by dsimp [H];linarith [one_div_pos.mpr hm]
  refine ⟨H,hH,?_⟩
  intro h hh L hL
  have hh1 : 1 ≤ h := hH.trans hh
  have hhp : 0 < h := by linarith
  have hpow : h ≤ h^(L+1) := by
    exact le_self_pow₀ hh1 (by omega : L+1 ≠ 0)
  have hi : 1/h < min δ₀ y₀ := by
    apply (div_lt_iff₀ hhp).2
    have hless : 1/(min δ₀ y₀) < h := by dsimp [H] at hh;linarith
    have ht := (div_lt_iff₀ hm).mp hless
    nlinarith
  have hismall : 1/h^(L+1) < min δ₀ y₀ := (one_div_le_one_div_of_le hhp hpow).trans_lt hi
  dsimp only
  have hδp : 0 < 1/h^(L+1) := by positivity
  refine ⟨⟨by linarith [hismall.trans_le (min_le_right _ _)],by linarith⟩,?_⟩
  have ht := hismall.trans_le (min_le_left _ _)
  linarith

lemma all_order_logZ_gap :
    ∃ M δ : ℝ, 0 < M ∧ 0 < δ ∧ ∀ h : ℝ, 0 < h → ∀ L : ℕ,
      ∀ V ∈ Ico (0:ℝ) y₀, y₀-V ≤ δ → V=y₀-1/h^(L+1) →
      ∀ Y ∈ Ico (0:ℝ) y₀,
      Real.log (Z Y)-Real.log (Z V) ≤ M+(5/2:ℝ)*((L:ℝ)+1)*Real.log h := by
  obtain ⟨M,δ,hM,hδ,hlog⟩ := Z_critical_log_bound
  refine ⟨|Real.log (Z 0)|+M,δ,by positivity,hδ,?_⟩
  intro h hh L V hV hsmall hVeq Y hY
  have hl := hlog V hV hsmall
  have heq : Real.log (y₀-V)=-((L:ℝ)+1)*Real.log h := by
    rw [hVeq,show y₀-(y₀-1/h^(L+1))=1/h^(L+1) by ring,
      Real.log_div (by norm_num) (pow_ne_zero _ hh.ne'),Real.log_one,Real.log_pow,Nat.cast_add,Nat.cast_one]
    ring
  rw [heq] at hl
  have hm := (abs_le.mp hl).1
  have hy := logZ_le_zero_parameter Y hY
  linarith [le_abs_self (Real.log (Z 0))]
end WP.Analysis
