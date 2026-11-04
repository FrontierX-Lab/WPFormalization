import WPFormalization.HigherOrder.OrderWeights
import WPFormalization.HigherOrder.WeightedCoefficientSum
import WPFormalization.HigherOrder.NormalizedCoefficientMajorants
import WPFormalization.Marked.DilatonRefinement

/-! The actual merger operator preserves the growing-order coefficient normalization under the lower-order induction bounds. Every infinite kernel series is proved summable. We use the valid analytic majorant exp(3t), and do not assert the sharper specific exp(t) inequality or the complete hierarchy bound. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma exp_coeff_nonneg : ∀n:ℕ,0≤PowerSeries.coeff n (PowerSeries.exp ℝ) := by
  intro n
  norm_num [PowerSeries.coeff_exp]

lemma merger_kernel_normalized_majorant : ∃ C M₀:ℝ,0<C ∧ 0<M₀ ∧
    ∀M:ℝ,M₀≤M→∀j:ℕ,∀Y∈Set.Icc (0:ℝ) y₀,∀F:HierarchyJet,∀e:Series,
      (∀n:ℕ,0≤PowerSeries.coeff n e)→
      (∀i:ℕ,i≤j→∀d:List ℕ,1≤d.length→|PowerSeries.coeff i (F.profile d)|≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)→
      ∀t:ℕ,∀d:List ℕ,∀k:ℕ,k<d.length→∀n:ℕ,n≤j→
        Summable (fun l:ℕ=>if 1≤t+d[k]!+l then weight Y l*
          PowerSeries.coeff n (complexityShift 1 (F.profile (mergerProfile t d l k))) else 0) ∧
        |PowerSeries.coeff n (coefficientSum (fun l:ℕ=>if 1≤t+d[k]!+l then
          PowerSeries.C (weight Y l)*complexityShift 1 (F.profile (mergerProfile t d l k)) else 0))|≤
          C*(profileOrderWeight M (j+1) (t::d))^(2*n)*
            PowerSeries.coeff n ((PowerSeries.exp ℝ)*e) := by
  obtain ⟨C,M₁,hC,hM₁,hkernel⟩:=canonical_coefficientSum_order_bounds
  refine ⟨C,max M₁ 1,hC,lt_of_lt_of_le hM₁ (le_max_left _ _),?_⟩
  intro M hM j Y hY F e he hprofile t d k hk n hn
  have hMop:M₁≤M:=(le_max_left _ _).trans hM
  have hM1:1≤M:=(le_max_right _ _).trans hM
  have hM0:0≤M:=by linarith
  let S:=profileOrderWeight M (j+1) (t::d)
  have hSJ:((j+1:ℕ):ℝ)≤S := by
    have hj:=mul_le_mul_of_nonneg_right hM1 (show (0:ℝ)≤((j+1:ℕ):ℝ) from Nat.cast_nonneg (j+1))
    dsimp [S,profileOrderWeight]
    nlinarith [show (0:ℝ)≤(t::d).sum from Nat.cast_nonneg _,show (0:ℝ)≤(t::d).length from Nat.cast_nonneg _]
  have hEN : ∀i:ℕ,0≤PowerSeries.coeff i ((PowerSeries.exp ℝ)*e):=coeff_mul_nonneg exp_coeff_nonneg he
  let L:ℕ→Series:=fun l=>if 1≤t+d[k]!+l then complexityShift 1 (F.profile (mergerProfile t d l k)) else 0
  have hL (l:ℕ) : |PowerSeries.coeff n (L l)|≤
      PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)*(S+l+1)^(2*n) := by
    have hSl : ((j+1:ℕ):ℝ)≤S+l+1:=by linarith [Nat.cast_nonneg (α:=ℝ) l]
    have hSl0:0≤S+l+1:=le_trans (Nat.cast_nonneg (j+1)) hSl
    by_cases hg:1≤t+d[k]!+l
    · dsimp [L]
      rw [if_pos hg]
      have hshift:=complexityShift_coeff_exponential_majorant 1 (S+l+1)
        (F.profile (mergerProfile t d l k)) (fun i=>PowerSeries.coeff i e) n (j+1)
        (by omega) (by norm_num) hSl he (by
          intro i hi
          have hlen:(mergerProfile t d l k).length=d.length:=by
            simp only [mergerProfile,List.length_cons,List.length_eraseIdx_of_lt hk]
            omega
          have hp:=hprofile i (hi.trans hn) (mergerProfile t d l k) (by rw [hlen];omega)
          have hw:=merger_order_weight M hM0 i (j+1) t l k d (by omega) hk hg
          have hw0:0≤profileOrderWeight M i (mergerProfile t d l k):=by unfold profileOrderWeight;positivity
          have hw':profileOrderWeight M i (mergerProfile t d l k)≤S+l+1:=by dsimp [S];linarith
          simpa only [mul_comm] using hp.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 hw' (2*i)) (he i)))
      have hemk : PowerSeries.mk (fun i=>PowerSeries.coeff i e)=e := by ext i;simp
      rw [hemk] at hshift
      simpa only [mul_comm] using hshift
    · simp only [L,if_neg hg,map_zero,abs_zero]
      exact mul_nonneg (hEN n) (pow_nonneg hSl0 _)
  have hop:=hkernel M hMop (j+1) (t::d).sum (t::d).length (2*n) n (by simp) (by omega)
    _ (hEN n) L Y hY hL
  have hseries : coefficientSum (fun l:ℕ=>if 1≤t+d[k]!+l then
      PowerSeries.C (weight Y l)*complexityShift 1 (F.profile (mergerProfile t d l k)) else 0)=
      coefficientSum (fun l:ℕ=>PowerSeries.C (weight Y l)*L l) := by
    apply congrArg coefficientSum
    funext l
    dsimp [L]
    split_ifs <;>simp
  constructor
  · convert! hop.1 using 1
    funext l
    dsimp [L]
    split_ifs <;>simp
  · rw [hseries]
    convert! hop.2.2.1 using 1 <;>dsimp [S,profileOrderWeight] <;>ring
lemma mergerSeries_normalized_majorant : ∃ C M₀:ℝ,0<C ∧ 0<M₀ ∧
    ∀M:ℝ,M₀≤M→∀j:ℕ,∀Y∈Set.Icc (0:ℝ) y₀,∀F:HierarchyJet,∀e g:Series,
      (∀n:ℕ,0≤PowerSeries.coeff n e)→(∀n:ℕ,0≤PowerSeries.coeff n g)→
      (∀i:ℕ,i≤j→∀d:List ℕ,1≤d.length→|PowerSeries.coeff i (F.profile d)|≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)→
      (∀i:ℕ,i≤j→∀p:ℕ,1≤p→|PowerSeries.coeff i (F.cusp p)|≤
        (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i g)→
      ∀t:ℕ,∀d:List ℕ,
      |PowerSeries.coeff (j+1) (mergerSeries Y F t d)|≤
        2*C*|A Y| * (profileOrderWeight M (j+1) (t::d))^(2*j+1)*
          PowerSeries.coeff j (((PowerSeries.exp ℝ)^3)*g*e) := by
  obtain ⟨C,M₁,hC,hM₁,hkernel⟩:=merger_kernel_normalized_majorant
  refine ⟨C,max M₁ 1,hC,lt_of_lt_of_le hM₁ (le_max_left _ _),?_⟩
  intro M hM j Y hY F e g he hg hprofile hcusp t d
  have hMop:M₁≤M:=(le_max_left _ _).trans hM
  have hM1:1≤M:=(le_max_right _ _).trans hM
  have hM0:0≤M:=by linarith
  let S:=profileOrderWeight M (j+1) (t::d)
  have hSJ:((j+1:ℕ):ℝ)≤S := by
    have hj:=mul_le_mul_of_nonneg_right hM1 (show (0:ℝ)≤((j+1:ℕ):ℝ) from Nat.cast_nonneg (j+1))
    dsimp [S,profileOrderWeight]
    nlinarith [show (0:ℝ)≤(t::d).sum from Nat.cast_nonneg _,show (0:ℝ)≤(t::d).length from Nat.cast_nonneg _]
  have hS0:0≤S:=(Nat.cast_nonneg (j+1)).trans hSJ
  have hE:=coeff_mul_nonneg exp_coeff_nonneg he
  have hG:=coeff_mul_nonneg exp_coeff_nonneg hg
  have hExp3:∀n:ℕ,0≤PowerSeries.coeff n ((PowerSeries.exp ℝ)^3):=by
    simpa only [pow_succ,pow_one,pow_zero,one_mul] using
      coeff_mul_nonneg (coeff_mul_nonneg exp_coeff_nonneg exp_coeff_nonneg) exp_coeff_nonneg
  have hTop:=coeff_mul_nonneg (coeff_mul_nonneg hExp3 hg) he
  by_cases hd:1≤d.length
  · let H:Series:=∑k∈Finset.range d.length,PowerSeries.C (2*(d[k]!:ℝ)+1)*
      coefficientSum (fun l:ℕ=>if 1≤t+d[k]!+l then PowerSeries.C (weight Y l)*
        complexityShift 1 (F.profile (mergerProfile t d l k)) else 0)
    let E:Series:=(PowerSeries.exp ℝ)*e
    let G:Series:=(PowerSeries.exp ℝ)*g
    let Q:Series:=PowerSeries.C (2*C*S)*E
    have hQ:∀n:ℕ,0≤PowerSeries.coeff n Q:=by
      intro n
      simp only [Q,PowerSeries.coeff_C_mul]
      exact mul_nonneg (by positivity) (hE n)
    have hH (n:ℕ) (hn:n≤j) : ‖PowerSeries.coeff n H‖≤S^(2*n)*PowerSeries.coeff n Q := by
      simp only [H,map_sum,PowerSeries.coeff_C_mul,Real.norm_eq_abs]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc _≤∑k∈Finset.range d.length,(2*(d[k]!:ℝ)+1)*(C*S^(2*n)*PowerSeries.coeff n E) := by
             apply Finset.sum_le_sum
             intro k hk
             rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*(d[k]!:ℝ)+1)]
             exact mul_le_mul_of_nonneg_left
               (hkernel M hMop j Y hY F e he hprofile t d k (Finset.mem_range.mp hk) n hn).2 (by positivity)
           _=(∑k∈Finset.range d.length,(2*(d[k]!:ℝ)+1))*(C*S^(2*n)*PowerSeries.coeff n E):=by rw [Finset.sum_mul]
           _≤(2*S)*(C*S^(2*n)*PowerSeries.coeff n E):=mul_le_mul_of_nonneg_right
             (merger_count_le_order_weight M hM0 (j+1) t d) (mul_nonneg (mul_nonneg hC.le (pow_nonneg hS0 _)) (hE n))
           _=S^(2*n)*PowerSeries.coeff n Q:=by dsimp only [Q];rw [PowerSeries.coeff_C_mul];ring
    have hCS (n:ℕ) (hn:n≤j) : ‖PowerSeries.coeff n (complexityShift 1 (F.cusp d.length))‖≤S^(2*n)*PowerSeries.coeff n G := by
      have hb:=complexityShift_coeff_exponential_majorant 1 S (F.cusp d.length)
        (fun i=>PowerSeries.coeff i g) n (j+1) (by omega) (by norm_num) hSJ hg (by
          intro i hi
          have hsc:scalarOrderWeight M i d.length≤S:=by
            have hm:=mul_le_mul_of_nonneg_left (show (i:ℝ)≤((j+1:ℕ):ℝ) by exact_mod_cast (show i≤j+1 by omega)) hM0
            dsimp [S,scalarOrderWeight,profileOrderWeight]
            simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
            norm_num only [Nat.cast_add,Nat.cast_one] at hm
            nlinarith [show (0:ℝ)≤t from Nat.cast_nonneg _,show (0:ℝ)≤d.sum from Nat.cast_nonneg _]
          have hs0:0 ≤ scalarOrderWeight M i d.length:=by unfold scalarOrderWeight;positivity
          simpa only [mul_comm] using (hcusp i (hi.trans hn) d.length hd).trans
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs0 hsc _) (hg i)))
      have hemk:PowerSeries.mk (fun i=>PowerSeries.coeff i g)=g:=by ext i;simp
      rw [hemk] at hb
      simpa only [Real.norm_eq_abs,G] using hb
    have hInv (n:ℕ) (hn:n≤j) : ‖PowerSeries.coeff n ((1-PowerSeries.C 1*PowerSeries.X : Series)⁻¹)‖≤
        S^(2*n)*PowerSeries.coeff n (PowerSeries.exp ℝ) := by
      have hb:=inverse_linear_pow_coeff_normalized 1 S 1 n (j+1) (by omega) (by omega) (by norm_num) hSJ
      have heq:PowerSeries.coeff n (PowerSeries.exp ℝ)=1/(n.factorial:ℝ):=by norm_num [PowerSeries.coeff_exp]
      simpa only [pow_one,Real.norm_eq_abs,heq,div_eq_mul_inv,one_mul] using hb
    have hProd:=scaled_coeff_mul_bound ((1-PowerSeries.C 1*PowerSeries.X : Series)⁻¹)
      (complexityShift 1 (F.cusp d.length)*H) (PowerSeries.exp ℝ) (G*Q) S hS0 j
      exp_coeff_nonneg (coeff_mul_nonneg hG hQ) hInv (by
        intro n hn
        exact scaled_coeff_mul_bound _ _ G Q S hS0 n hG hQ
          (fun i hi=>hCS i (hi.trans hn)) (fun i hi=>hH i (hi.trans hn)))
    have hser:mergerSeries Y F t d=PowerSeries.C (A Y)*(PowerSeries.X^1*
        (((1-PowerSeries.C 1*PowerSeries.X : Series)⁻¹)*(complexityShift 1 (F.cusp d.length)*H))) := by
      dsimp [mergerSeries,H,mergerProfile]
      unfold shiftVariable
      ring
    have hmaj:(PowerSeries.exp ℝ)*(G*Q)=PowerSeries.C (2*C*S)*(((PowerSeries.exp ℝ)^3)*g*e) := by
      dsimp [G,Q,E]
      ring
    rw [hmaj,PowerSeries.coeff_C_mul] at hProd
    rw [hser,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul,abs_mul]
    apply (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hProd) (abs_nonneg (A Y))).trans_eq
    dsimp only [S]
    rw [pow_succ]
    ring
  · have he:d=[]:=List.eq_nil_of_length_eq_zero (by omega)
    rw [he]
    simp only [mergerSeries,List.length_nil,Finset.range_zero,Finset.sum_empty,mul_zero,map_zero,abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC.le) (abs_nonneg _))
      (by unfold profileOrderWeight;positivity)) (hTop j)
lemma mergerSeries_uniform_normalized_majorant : ∃ B M₀:ℝ,0<B ∧ 0<M₀ ∧
    ∀M:ℝ,M₀≤M→∀j:ℕ,∀Y∈Set.Icc (0:ℝ) y₀,∀F:HierarchyJet,∀e g:Series,
      (∀n:ℕ,0≤PowerSeries.coeff n e)→(∀n:ℕ,0≤PowerSeries.coeff n g)→
      (∀i:ℕ,i≤j→∀d:List ℕ,1≤d.length→|PowerSeries.coeff i (F.profile d)|≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)→
      (∀i:ℕ,i≤j→∀p:ℕ,1≤p→|PowerSeries.coeff i (F.cusp p)|≤
        (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i g)→
      ∀t:ℕ,∀d:List ℕ,
      |PowerSeries.coeff (j+1) (mergerSeries Y F t d)|≤
        B*(profileOrderWeight M (j+1) (t::d))^(2*j+1)*PowerSeries.coeff j (((PowerSeries.exp ℝ)^3)*g*e) := by
  obtain ⟨C,M₀,hC,hM₀,hdata⟩:=mergerSeries_normalized_majorant
  obtain ⟨A₀,hA₀,hA⟩:=dilaton_A_abs_uniform
  refine ⟨2*C*A₀,M₀,by positivity,hM₀,?_⟩
  intro M hM j Y hY F e g he hg hprofile hcusp t d
  have hi:=hdata M hM j Y hY F e g he hg hprofile hcusp t d
  have hMpos:0<M:=lt_of_lt_of_le hM₀ hM
  have hS:0≤profileOrderWeight M (j+1) (t::d):=by unfold profileOrderWeight;positivity
  have hExp3:∀n:ℕ,0≤PowerSeries.coeff n ((PowerSeries.exp ℝ)^3):=by
    simpa only [pow_succ,pow_one,pow_zero,one_mul] using
      coeff_mul_nonneg (coeff_mul_nonneg exp_coeff_nonneg exp_coeff_nonneg) exp_coeff_nonneg
  have hTop:=coeff_mul_nonneg (coeff_mul_nonneg hExp3 hg) he
  apply hi.trans
  have hb:=mul_le_mul_of_nonneg_right (hA Y hY)
    (mul_nonneg (mul_nonneg (by positivity : 0≤2*C) (pow_nonneg hS (2*j+1))) (hTop j))
  convert! hb using 1 <;>ring
end WP.HigherOrder
