import Mathlib
/-! A finite-rank substitute for the bounded stopped-chain argument.
An explicit truncated survival barrier controls exits using the exponential
zero potential. The proved mass discount and terminal envelope then yield
the logarithmic lower bound, with all constants independent of the state.
This is a generic lemma: clients must prove every local transition property. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

def survivalBarrier (K B : ℝ) (h z : ℕ) : ℝ :=
  max 0 (1 - ((2 : ℝ)^z + (h : ℝ)*K)/B)
lemma survivalBarrier_nonneg (K B : ℝ) (h z : ℕ) : 0 ≤ survivalBarrier K B h z := le_max_left _ _
lemma survivalBarrier_le_one (K B : ℝ) (hK : 0 ≤ K) (hB : 0 < B) (h z : ℕ) :
    survivalBarrier K B h z ≤ 1 := by
  apply max_le zero_le_one
  have hh : 0 ≤ ((2 : ℝ)^z + (h : ℝ)*K)/B := by positivity
  linarith
lemma finite_survivalBarrier_step {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℕ)
    (K B mass : ℝ) (h Z : ℕ) (hh : 1 ≤ h) (hK : 0 ≤ K) (hB : 0 < B)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = mass)
    (hpot : (∑ i ∈ s, w i*(2 : ℝ)^(z i)) ≤ mass*((2 : ℝ)^Z + K)) :
    mass*survivalBarrier K B h Z ≤ ∑ i ∈ s, w i*survivalBarrier K B (h-1) (z i) := by
  have hm : 0 ≤ mass := by rw [←hsum];exact Finset.sum_nonneg hw
  have hnonneg : 0 ≤ ∑ i ∈ s, w i*survivalBarrier K B (h-1) (z i) :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (survivalBarrier_nonneg _ _ _ _))
  have hlinear : ∑ i ∈ s, w i*(1-((2 : ℝ)^(z i)+((h-1 : ℕ):ℝ)*K)/B) =
      mass - ((∑ i ∈ s, w i*(2 : ℝ)^(z i)) + ((h-1 : ℕ):ℝ)*K*mass)/B := by
    simp_rw [mul_sub,mul_one,←mul_div_assoc,mul_add]
    rw [Finset.sum_sub_distrib,←Finset.sum_div,Finset.sum_add_distrib,hsum,←Finset.sum_mul,hsum]
    ring
  have hraw : mass*(1-((2 : ℝ)^Z+(h : ℝ)*K)/B) ≤
      ∑ i ∈ s, w i*survivalBarrier K B (h-1) (z i) := by
    have hsmall : ∑ i ∈ s, w i*(1-((2 : ℝ)^(z i)+((h-1 : ℕ):ℝ)*K)/B) ≤
        ∑ i ∈ s, w i*survivalBarrier K B (h-1) (z i) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (le_max_right _ _) (hw i hi))
    rw [hlinear] at hsmall
    have hcast : ((h-1 : ℕ):ℝ) = (h : ℝ)-1 := by rw [Nat.cast_sub hh,Nat.cast_one]
    have he : mass*(1-((2 : ℝ)^Z+(h : ℝ)*K)/B) =
        mass - (mass*((2 : ℝ)^Z+K)+((h-1 : ℕ):ℝ)*K*mass)/B := by rw [hcast];ring
    rw [he]
    apply le_trans _ hsmall
    apply sub_le_sub_left
    apply div_le_div_of_nonneg_right _ hB.le
    simpa only[add_comm] using add_le_add_right hpot (((h-1 : ℕ):ℝ)*K*mass)
  unfold survivalBarrier
  rw [mul_max_of_nonneg _ _ hm,mul_zero]
  exact max_le (by simpa only[survivalBarrier] using hnonneg) hraw

lemma log_successor_gap (h : ℝ) (hh : 1 ≤ h) : 1/(2*h) ≤ Real.log (h+1)-Real.log h := by
  have hp : 0 < h := by linarith
  have hp1 : 0 < h+1 := by linarith
  have he := Real.log_le_sub_one_of_pos (div_pos hp hp1)
  rw [Real.log_div hp.ne' hp1.ne'] at he
  have hfrac : h/(h+1)-1 = -1/(h+1) := by field_simp;ring
  rw [hfrac] at he
  have hhalf : 1/(2*h) ≤ 1/(h+1) := div_le_div_of_nonneg_left (by norm_num) hp1 (by linarith)
  simp only[neg_div] at he
  linarith
lemma exponential_rank_discount (D M : ℝ) (h : ℕ) (hD : 2 ≤ D) (hM : 0 ≤ M) (hh : 2 ≤ h) :
    Real.exp (-D*M*(1+Real.log ((h:ℝ)+1))) ≤
      Real.exp (-M/(h:ℝ))*Real.exp (-D*M*(1+Real.log (h:ℝ))) := by
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hhR : (1:ℝ) ≤ h := by exact_mod_cast (by omega : 1 ≤ h)
  have hp : (0:ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hg := log_successor_gap (h:ℝ) hhR
  have hgp : 0 ≤ Real.log ((h:ℝ)+1)-Real.log (h:ℝ) := by linarith [one_div_pos.mpr (show 0 < 2*(h:ℝ) by positivity)]
  have he := mul_le_mul_of_nonneg_right hD (mul_nonneg hM hgp)
  have hf := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*M by positivity)
  have hi : 2*M*(1/(2*(h:ℝ))) = M/(h:ℝ) := by ring
  simp only[neg_div]
  nlinarith
end WP.Analysis
namespace WP.Analysis
open Set Filter
open scoped Topology
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma finite_rank_lower_barrier_dependent {α : Type*} (ι : α → Type*) [∀ x, Fintype (ι x)]
    (rank Z : α → ℕ) (R : α → ℝ) (T : α → Prop)
    (child : ∀ x, ι x → α) (w : ∀ x, ι x → ℝ)
    (c Ct D K B M : ℝ) (hc : 0 < c) (hCt : 0 ≤ Ct) (hD : 2 ≤ D) (hDC : Ct ≤ D)
    (hK : 0 ≤ K) (hB : 0 < B) (hM : 0 ≤ M)
    (hthreshold : ∀ z : ℕ, (2 : ℝ)^z < B → (z : ℝ) ≤ M)
    (hRank : ∀ x, 1 ≤ rank x) (hR : ∀ x, 0 ≤ R x)
    (hterminal : ∀ x, T x → c*Real.exp (-Ct*(Z x : ℝ)) ≤ R x)
    (hlarge : ∀ x, ¬T x → 2 ≤ rank x)
    (hw : ∀ x, ∀ i ∈ (Finset.univ : Finset (ι x)), 0 ≤ w x i)
    (hdrop : ∀ x, ¬T x → ∀ i ∈ (Finset.univ : Finset (ι x)), w x i ≠ 0 → rank (child x i)+1 = rank x)
    (hmass : ∀ x, ¬T x → Real.exp (-(Z x : ℝ)/(rank x : ℝ)) ≤ ∑ i : ι x, w x i)
    (hpot : ∀ x, ¬T x → (∑ i : ι x, w x i*(2 : ℝ)^(Z (child x i))) ≤
      (∑ i : ι x, w x i)*((2 : ℝ)^(Z x)+K))
    (hsuper : ∀ x, ¬T x → (∑ i : ι x, w x i*R (child x i)) ≤ R x) :
    ∀ x, c*Real.exp (-D*M*(1+Real.log ((rank x : ℝ)+1)))*survivalBarrier K B (rank x) (Z x) ≤ R x := by
  classical
  suffices hmain : ∀ h : ℕ, ∀ x, rank x = h →
      c*Real.exp (-D*M*(1+Real.log ((h : ℝ)+1)))*survivalBarrier K B h (Z x) ≤ R x by
    intro x
    exact hmain _ x rfl
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro x he
    have hh1 : 1 ≤ h := by simpa only[he] using hRank x
    have hhpos : 0 < (h : ℝ) := by exact_mod_cast (by omega : 0 < h)
    by_cases hb : survivalBarrier K B h (Z x) = 0
    · rw[hb,mul_zero]
      exact hR x
    have hbpos : 0 < survivalBarrier K B h (Z x) :=
      lt_of_le_of_ne (survivalBarrier_nonneg _ _ _ _) (Ne.symm hb)
    have hZM : (Z x : ℝ) ≤ M := by
      have hraw : 0 < 1-((2 : ℝ)^(Z x)+(h : ℝ)*K)/B :=
        (lt_max_iff.mp hbpos).resolve_left (lt_irrefl 0)
      have hq : ((2 : ℝ)^(Z x)+(h : ℝ)*K)/B < 1 := by linarith
      have hq' := (div_lt_one hB).mp hq
      exact hthreshold _ (lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hq')
    by_cases ht : T x
    · have hlog : 0 ≤ Real.log ((h : ℝ)+1) := Real.log_nonneg (by have hn:(0:ℝ)≤h:=Nat.cast_nonneg _;linarith)
      have hD0 : 0 ≤ D := by linarith
      have hcost₁ : Ct*(Z x : ℝ) ≤ D*M := mul_le_mul hDC hZM (Nat.cast_nonneg _) hD0
      have hcost₂ : D*M ≤ D*M*(1+Real.log ((h : ℝ)+1)) := by
        have hp := mul_nonneg (mul_nonneg hD0 hM) hlog
        nlinarith
      have hExp : Real.exp (-D*M*(1+Real.log ((h : ℝ)+1))) ≤ Real.exp (-Ct*(Z x : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc _ ≤ c*Real.exp (-D*M*(1+Real.log ((h : ℝ)+1))) := by
                simpa only[mul_one] using mul_le_mul_of_nonneg_left (survivalBarrier_le_one K B hK hB h (Z x))
                  (show 0 ≤ c*Real.exp (-D*M*(1+Real.log ((h : ℝ)+1))) by positivity)
           _ ≤ c*Real.exp (-Ct*(Z x : ℝ)) := mul_le_mul_of_nonneg_left hExp hc.le
           _ ≤ R x := hterminal x ht
    · have hh2 : 2 ≤ h := by simpa only[he] using hlarge x ht
      let A := Real.exp (-D*M*(1+Real.log (h : ℝ)))
      let mass := ∑ i : ι x, w x i
      have hA : 0 < A := Real.exp_pos _
      have hMass : Real.exp (-M/(h : ℝ)) ≤ mass := by
        apply le_trans _ (by simpa only[he] using hmass x ht)
        apply Real.exp_le_exp.mpr
        simpa only[neg_div] using neg_le_neg (div_le_div_of_nonneg_right hZM hhpos.le)
      have hsum : c*A*(∑ i : ι x, w x i*survivalBarrier K B (h-1) (Z (child x i))) ≤
          ∑ i : ι x, w x i*R (child x i) := by
        have hpoint : ∀ i ∈ (Finset.univ : Finset (ι x)), w x i*(c*A*survivalBarrier K B (h-1) (Z (child x i))) ≤ w x i*R (child x i) := by
          intro i hi
          by_cases hwi : w x i = 0
          · simp[hwi]
          have hd := hdrop x ht i hi hwi
          rw[he] at hd
          have hl : rank (child x i) < h := by omega
          have hr : rank (child x i) = h-1 := by omega
          have hhcast : ((h-1 : ℕ):ℝ)+1 = (h : ℝ) := by rw[Nat.cast_sub hh1,Nat.cast_one];ring
          have hInd := ih _ hl (child x i) rfl
          rw[hr,hhcast] at hInd
          exact mul_le_mul_of_nonneg_left hInd (hw x i hi)
        calc _ = ∑ i : ι x, w x i*(c*A*survivalBarrier K B (h-1) (Z (child x i))) := by
                  rw[Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
             _ ≤ _ := Finset.sum_le_sum hpoint
      have hbar : mass*survivalBarrier K B h (Z x) ≤
          ∑ i : ι x, w x i*survivalBarrier K B (h-1) (Z (child x i)) :=
        finite_survivalBarrier_step (Finset.univ : Finset (ι x)) (w x) (fun i=>Z (child x i)) K B mass h (Z x)
          hh1 hK hB (hw x) rfl (hpot x ht)
      have hdisc : Real.exp (-D*M*(1+Real.log ((h : ℝ)+1))) ≤ Real.exp (-M/(h : ℝ))*A :=
        exponential_rank_discount D M h hD hM hh2
      calc _ ≤ c*(Real.exp (-M/(h : ℝ))*A)*survivalBarrier K B h (Z x) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdisc hc.le) (survivalBarrier_nonneg _ _ _ _)
           _ ≤ c*(mass*A)*survivalBarrier K B h (Z x) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMass hA.le) hc.le)
                  (survivalBarrier_nonneg _ _ _ _)
           _ = c*A*(mass*survivalBarrier K B h (Z x)) := by ring
           _ ≤ c*A*(∑ i : ι x, w x i*survivalBarrier K B (h-1) (Z (child x i))) :=
                mul_le_mul_of_nonneg_left hbar (by positivity)
           _ ≤ ∑ i : ι x, w x i*R (child x i) := hsum
           _ ≤ R x := hsuper x ht
end WP.Analysis
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma finite_rank_log_lower {α : Type*} (ι : α → Type*) [∀ x, Fintype (ι x)]
    (rank Z : α → ℕ) (R : α → ℝ) (T : α → Prop)
    (child : ∀ x, ι x → α) (w : ∀ x, ι x → ℝ)
    (c Ct : ℝ) (hc : 0 < c) (hCt : 0 ≤ Ct)
    (hRank : ∀ x, 1 ≤ rank x) (hR : ∀ x, 0 ≤ R x)
    (hterminal : ∀ x, T x → c*Real.exp (-Ct*(Z x : ℝ)) ≤ R x)
    (hlarge : ∀ x, ¬T x → 2 ≤ rank x)
    (hw : ∀ x, ∀ i ∈ (Finset.univ : Finset (ι x)), 0 ≤ w x i)
    (hdrop : ∀ x, ¬T x → ∀ i ∈ (Finset.univ : Finset (ι x)), w x i ≠ 0 → rank (child x i)+1 = rank x)
    (hmass : ∀ x, ¬T x → Real.exp (-(Z x : ℝ)/(rank x : ℝ)) ≤ ∑ i : ι x, w x i)
    (hpot : ∀ x, ¬T x → (∑ i : ι x, w x i*(2 : ℝ)^(Z (child x i))) ≤
      (∑ i : ι x, w x i)*((2 : ℝ)^(Z x)+(2 : ℝ)^26))
    (hsuper : ∀ x, ¬T x → (∑ i : ι x, w x i*R (child x i)) ≤ R x) :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧ ∀ x,
      c₀*Real.exp (-C*((Z x : ℝ)+Real.log ((rank x : ℝ)+1))*Real.log ((rank x : ℝ)+1)) ≤ R x := by
  let ℓ : ℝ := Real.log 2
  let D : ℝ := max Ct 2
  let Q : ℝ := max 1 (28/ℓ)
  let C : ℝ := D*Q*(1+1/ℓ)
  have hℓ : 0 < ℓ := Real.log_pos (by norm_num)
  have hD : 2 ≤ D := le_max_right _ _
  have hDC : Ct ≤ D := le_max_left _ _
  have hD0 : 0 < D := by linarith
  have hQ : 1 ≤ Q := le_max_left _ _
  have hQ' : 28/ℓ ≤ Q := le_max_right _ _
  have hC : 0 < C := by dsimp[C];positivity
  refine ⟨c/2,C,by positivity,hC,?_⟩
  intro x
  let H := rank x
  let z := Z x
  let K : ℝ := (2 : ℝ)^26
  let B : ℝ := 2*((2 : ℝ)^z+(H : ℝ)*K)
  let M : ℝ := Real.log B/ℓ
  let L : ℝ := Real.log ((H : ℝ)+1)
  have hH : 1 ≤ H := hRank x
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hHp : 0 < (H : ℝ)+1 := by positivity
  have hPow : 1 ≤ (2 : ℝ)^z := one_le_pow₀ (by norm_num)
  have hK : 1 ≤ K := by norm_num[K]
  have hB : 0 < B := by dsimp[B];positivity
  have hB1 : 1 ≤ B := by dsimp[B];nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) H) (by positivity : 0 ≤ K)]
  have hM : 0 ≤ M := div_nonneg (Real.log_nonneg hB1) hℓ.le
  have hL : ℓ ≤ L := by
    apply Real.log_le_log (by norm_num)
    have hhR : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  have hL0 : 0 ≤ L := (hℓ.trans_le hL).le
  have hthreshold : ∀ n : ℕ, (2 : ℝ)^n < B → (n : ℝ) ≤ M := by
    intro n hn
    have hl := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) n) hn.le
    rw[Real.log_pow] at hl
    apply (le_div_iff₀ hℓ).mpr
    exact hl
  have hBarrier := finite_rank_lower_barrier_dependent ι rank Z R T child w c Ct D K B M hc hCt hD hDC
    (by positivity) hB hM hthreshold hRank hR hterminal hlarge hw hdrop hmass hpot hsuper x
  have hBar : survivalBarrier K B H z = 1/2 := by
    have ht : 0 < (2 : ℝ)^z+(H : ℝ)*K := by positivity
    have he : ((2 : ℝ)^z+(H : ℝ)*K)/B = 1/2 := by dsimp[B];field_simp
    unfold survivalBarrier
    rw[he]
    norm_num
  change c*Real.exp (-D*M*(1+L))*survivalBarrier K B H z ≤ R x at hBarrier
  rw[hBar] at hBarrier
  have hBB : B ≤ (2 : ℝ)^(z+27)*((H : ℝ)+1) := by
    dsimp[B,K]
    rw[pow_add]
    have h₁ := mul_nonneg (show (0:ℝ)≤(2:ℝ)^26-1 by norm_num) (show 0≤(2:ℝ)^z by positivity)
    have h₂ := mul_nonneg (show (0:ℝ)≤(H:ℝ)*(2:ℝ)^26 by positivity) (show 0≤(2:ℝ)^z-1 by linarith)
    norm_num only[pow_succ] at *
    nlinarith
  have hLogB : Real.log B ≤ ((z : ℝ)+27)*ℓ+L := by
    have hh := Real.log_le_log hB hBB
    rw[Real.log_mul (pow_ne_zero _ (by norm_num : (2:ℝ)≠0)) hHp.ne',Real.log_pow] at hh
    simpa only[Nat.cast_add,Nat.cast_ofNat] using hh
  have hMid : M ≤ (z : ℝ)+27+L/ℓ := by
    calc M ≤ (((z:ℝ)+27)*ℓ+L)/ℓ := div_le_div_of_nonneg_right hLogB hℓ.le
         _ = _ := by field_simp
  have h27 : 27 ≤ (27/ℓ)*L := by
    have hh := mul_le_mul_of_nonneg_left hL (show 0≤(27/ℓ:ℝ) by positivity)
    rw[div_mul_cancel₀ _ hℓ.ne'] at hh
    exact hh
  have hM' : M ≤ (z : ℝ)+(28/ℓ)*L := by
    calc M ≤ (z:ℝ)+27+L/ℓ := hMid
         _ ≤ (z:ℝ)+(27/ℓ)*L+L/ℓ := by linarith
         _ = _ := by ring
  have hMQ : M ≤ Q*((z : ℝ)+L) := by
    have h₁ := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg (α:=ℝ) z)
    have h₂ := mul_le_mul_of_nonneg_right hQ' hL0
    nlinarith
  have hLfactor : 1+L ≤ (1+1/ℓ)*L := by
    have hh := mul_le_mul_of_nonneg_left hL (show 0≤(1/ℓ:ℝ) by positivity)
    rw[one_div_mul_cancel hℓ.ne'] at hh
    nlinarith
  have hCost : D*M*(1+L) ≤ C*((z : ℝ)+L)*L := by
    calc _ ≤ D*(Q*((z:ℝ)+L))*(1+L) :=
               mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMQ hD0.le) (by positivity)
         _ ≤ D*(Q*((z:ℝ)+L))*((1+1/ℓ)*L) :=
               mul_le_mul_of_nonneg_left hLfactor (by positivity)
         _ = _ := by dsimp[C];ring
  change (c/2)*Real.exp (-C*((z : ℝ)+L)*L) ≤ R x
  calc _ ≤ (c/2)*Real.exp (-D*M*(1+L)) := by
             apply mul_le_mul_of_nonneg_left _ (by positivity)
             apply Real.exp_le_exp.mpr
             nlinarith
       _ = c*Real.exp (-D*M*(1+L))*(1/2) := by ring
       _ ≤ R x := hBarrier
end WP.Analysis
