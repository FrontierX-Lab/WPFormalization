import WPFormalization.HigherOrder.MergerMajorant

/-! The actual nonseparating operator: growing-order local coefficient bounds. Infinite kernel sums are proved summable from lower-order profile data. The valid analytic majorant is exp(3t); this is not the sharper particular C.25 inequality or the complete hierarchy estimate. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma handle_kernel_normalized_majorant : ∃ C M₀:ℝ,0<C ∧ 0<M₀ ∧
    ∀M:ℝ,M₀≤M→∀j:ℕ,∀Y∈Set.Icc (0:ℝ) y₀,∀F:HierarchyJet,∀e:Series,
      (∀n:ℕ,0≤PowerSeries.coeff n e)→
      (∀i:ℕ,i≤j→∀d:List ℕ,1≤d.length→|PowerSeries.coeff i (F.profile d)|≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)→
      ∀t:ℕ,∀d:List ℕ,∀n:ℕ,n≤j→
        Summable (fun l:ℕ=>weight Y l*PowerSeries.coeff n
          (∑u∈Finset.range (t+l-1),complexityShift 1 (F.profile (contractionProfile t d l u)))) ∧
        |PowerSeries.coeff n (coefficientSum (fun l:ℕ=>PowerSeries.C (weight Y l)*
          ∑u∈Finset.range (t+l-1),complexityShift 1 (F.profile (contractionProfile t d l u))))|≤
          C*(profileOrderWeight M (j+1) (t::d))^(2*n+1)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e) := by
  obtain ⟨C,M₁,hC,hM₁,hkernel⟩:=canonical_coefficientSum_order_bounds
  refine ⟨C,max M₁ 1,hC,lt_of_lt_of_le hM₁ (le_max_left _ _),?_⟩
  intro M hM j Y hY F e he hprofile t d n hn
  have hMop:M₁≤M:=(le_max_left _ _).trans hM
  have hM1:1≤M:=(le_max_right _ _).trans hM
  have hM0:0≤M:=by linarith
  let S:=profileOrderWeight M (j+1) (t::d)
  have hSJ:((j+1:ℕ):ℝ)≤S := by
    have hj:=mul_le_mul_of_nonneg_right hM1 (show (0:ℝ)≤((j+1:ℕ):ℝ) from Nat.cast_nonneg (j+1))
    dsimp [S,profileOrderWeight]
    nlinarith [show (0:ℝ)≤(t::d).sum from Nat.cast_nonneg _,show (0:ℝ)≤(t::d).length from Nat.cast_nonneg _]
  have hEN : ∀i:ℕ,0≤PowerSeries.coeff i ((PowerSeries.exp ℝ)*e):=coeff_mul_nonneg exp_coeff_nonneg he
  let L:ℕ→Series:=fun l=>∑u∈Finset.range (t+l-1),complexityShift 1 (F.profile (contractionProfile t d l u))
  have hL (l:ℕ) : |PowerSeries.coeff n (L l)|≤
      PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)*(S+l+1)^(2*n+1) := by
    have hSl : ((j+1:ℕ):ℝ)≤S+l+1:=by linarith [Nat.cast_nonneg (α:=ℝ) l]
    have hSl0:0≤S+l+1:=(Nat.cast_nonneg (j+1)).trans hSl
    have hpoint (u:ℕ) (hu:u∈Finset.range (t+l-1)) :
        |PowerSeries.coeff n (complexityShift 1 (F.profile (contractionProfile t d l u)))|≤
        (S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e) := by
      have hshift:=complexityShift_coeff_exponential_majorant 1 (S+l+1)
        (F.profile (contractionProfile t d l u)) (fun i=>PowerSeries.coeff i e) n (j+1)
        (by omega) (by norm_num) hSl he (by
          intro i hi
          have hp:=hprofile i (hi.trans hn) (contractionProfile t d l u) (by simp [contractionProfile])
          have hw:=handle_order_weight M hM0 i (j+1) t l u d (by omega) (Finset.mem_range.mp hu)
          have hw0:0≤profileOrderWeight M i (contractionProfile t d l u):=by unfold profileOrderWeight;positivity
          have hw':profileOrderWeight M i (contractionProfile t d l u)≤S+l+1:=by dsimp [S];linarith
          simpa only [mul_comm] using hp.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 hw' (2*i)) (he i)))
      have hemk:PowerSeries.mk (fun i=>PowerSeries.coeff i e)=e:=by ext i;simp
      rw [hemk] at hshift
      exact hshift
    simp only [L,map_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc _≤∑u∈Finset.range (t+l-1),(S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e) :=
           Finset.sum_le_sum hpoint
         _=((t+l-1:ℕ):ℝ)*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)) := by
           simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
         _≤(S+l+1)*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)) :=
           mul_le_mul_of_nonneg_right
             ((pair_count_le_order_weight M hM0 (j+1) t l d).trans (by dsimp [S];linarith))
             (mul_nonneg (pow_nonneg hSl0 _) (hEN n))
         _=_:=by rw [pow_succ];ring
  have hop:=hkernel M hMop (j+1) (t::d).sum (t::d).length (2*n+1) n (by simp) (by omega)
    _ (hEN n) L Y hY hL
  refine ⟨hop.1,?_⟩
  convert! hop.2.2.1 using 1 <;>dsimp [S,profileOrderWeight] <;>ring
lemma nonseparatingSeries_normalized_majorant : ∃ C M₀:ℝ,0<C ∧ 0<M₀ ∧
    ∀M:ℝ,M₀≤M→∀j:ℕ,∀Y∈Set.Icc (0:ℝ) y₀,∀F:HierarchyJet,∀e g a:Series,
      (∀n:ℕ,0≤PowerSeries.coeff n e)→(∀n:ℕ,0≤PowerSeries.coeff n g)→(∀n:ℕ,0≤PowerSeries.coeff n a)→
      (∀i:ℕ,i≤j→∀d:List ℕ,1≤d.length→|PowerSeries.coeff i (F.profile d)|≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)→
      (∀i:ℕ,i≤j→∀p:ℕ,1≤p→|PowerSeries.coeff i (F.cusp p)|≤
        (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i g)→
      (∀i:ℕ,i≤j→∀p:ℕ,1≤p→|PowerSeries.coeff i (F.genus p)|≤
        (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i a)→
      ∀t:ℕ,∀d:List ℕ,
      |PowerSeries.coeff (j+1) (nonseparatingSeries Y F t d)|≤
        2*C*|A Y| * (profileOrderWeight M (j+1) (t::d))^(2*j+1)*
          PowerSeries.coeff j (((PowerSeries.exp ℝ)^3)*g*a*e) := by
  obtain ⟨C,M₁,hC,hM₁,hkernel⟩:=handle_kernel_normalized_majorant
  refine ⟨C,max M₁ 1,hC,lt_of_lt_of_le hM₁ (le_max_left _ _),?_⟩
  intro M hM j Y hY F e g a he hg ha hprofile hcusp hgenus t d
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
  let H:Series:=coefficientSum (fun l:ℕ=>PowerSeries.C (weight Y l)*
    ∑u∈Finset.range (t+l-1),complexityShift 1 (F.profile (contractionProfile t d l u)))
  let E:Series:=(PowerSeries.exp ℝ)*e
  let G:Series:=(PowerSeries.exp ℝ)*g
  let Q:Series:=PowerSeries.C (C*S)*E
  have hQ:∀n:ℕ,0≤PowerSeries.coeff n Q:=by
    intro n
    simp only [Q,PowerSeries.coeff_C_mul]
    exact mul_nonneg (by positivity) (hE n)
  have hH (n:ℕ) (hn:n≤j) : ‖PowerSeries.coeff n H‖≤S^(2*n)*PowerSeries.coeff n Q := by
    have hb:=(hkernel M hMop j Y hY F e he hprofile t d n hn).2
    rw [Real.norm_eq_abs]
    dsimp only [Q]
    rw [PowerSeries.coeff_C_mul]
    convert! hb using 1 <;>dsimp only [S,H,E] <;>rw [pow_succ] <;>ring

  have hbase:scalarOrderWeight M (j+1) (t::d).length≤S := by
    dsimp [S,profileOrderWeight,scalarOrderWeight]
    linarith [show (0:ℝ)≤(t::d).sum from Nat.cast_nonneg _]
  have hCS (n:ℕ) (hn:n≤j) : ‖PowerSeries.coeff n (complexityShift 1 (F.cusp (d.length+2)))‖≤
      S^(2*n)*PowerSeries.coeff n G := by
    have hb:=complexityShift_coeff_exponential_majorant 1 S (F.cusp (d.length+2))
      (fun i=>PowerSeries.coeff i g) n (j+1) (by omega) (by norm_num) hSJ hg (by
        intro i hi
        have hsc:= (scalar_order_weight_shift M hM1 i (j+1) (t::d).length (d.length+2) 1
          (by simp) (by omega)).trans hbase
        have hs0:0 ≤ scalarOrderWeight M i (d.length+2):=by unfold scalarOrderWeight;positivity
        simpa only [mul_comm] using (hcusp i (hi.trans hn) (d.length+2) (by omega)).trans
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs0 hsc _) (hg i)))
    have hemk:PowerSeries.mk (fun i=>PowerSeries.coeff i g)=g:=by ext i;simp
    rw [hemk] at hb
    simpa only [Real.norm_eq_abs,G] using hb
  have hGen (n:ℕ) (hn:n≤j) : ‖PowerSeries.coeff n (F.genus (d.length+1))‖≤S^(2*n)*PowerSeries.coeff n a := by
    have hsc:scalarOrderWeight M n (d.length+1)≤S :=
      (scalar_order_weight_shift M hM1 n (j+1) (t::d).length (d.length+1) 0 (by simp) (by omega)).trans hbase
    have hs0:0 ≤ scalarOrderWeight M n (d.length+1):=by unfold scalarOrderWeight;positivity
    simpa only [Real.norm_eq_abs] using (hgenus n hn (d.length+1) (by omega)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs0 hsc _) (ha n))
  have hInv (n:ℕ) (hn:n≤j) : ‖PowerSeries.coeff n ((1-PowerSeries.C 1*PowerSeries.X : Series)⁻¹)‖≤
      S^(2*n)*PowerSeries.coeff n (PowerSeries.exp ℝ) := by
    have hb:=inverse_linear_pow_coeff_normalized 1 S 1 n (j+1) (by omega) (by omega) (by norm_num) hSJ
    have heq:PowerSeries.coeff n (PowerSeries.exp ℝ)=1/(n.factorial:ℝ):=by norm_num [PowerSeries.coeff_exp]
    simpa only [pow_one,Real.norm_eq_abs,heq,div_eq_mul_inv,one_mul] using hb
  have hProd:=scaled_coeff_mul_bound ((1-PowerSeries.C 1*PowerSeries.X : Series)⁻¹)
    (complexityShift 1 (F.cusp (d.length+2))*(F.genus (d.length+1)*H))
    (PowerSeries.exp ℝ) (G*(a*Q)) S hS0 j exp_coeff_nonneg (coeff_mul_nonneg hG (coeff_mul_nonneg ha hQ)) hInv (by
      intro n hn
      exact scaled_coeff_mul_bound _ _ G (a*Q) S hS0 n hG (coeff_mul_nonneg ha hQ)
        (fun i hi=>hCS i (hi.trans hn)) (by
          intro i hi
          exact scaled_coeff_mul_bound _ _ a Q S hS0 i ha hQ
            (fun k hk=>hGen k (hk.trans (hi.trans hn))) (fun k hk=>hH k (hk.trans (hi.trans hn)))))
  have hser:nonseparatingSeries Y F t d=PowerSeries.C (2*A Y)*(PowerSeries.X^1*
      (((1-PowerSeries.C 1*PowerSeries.X : Series)⁻¹)*(complexityShift 1 (F.cusp (d.length+2))*(F.genus (d.length+1)*H)))) := by
    dsimp [nonseparatingSeries,H,contractionProfile]
    unfold shiftVariable
    ring
  have hmaj:(PowerSeries.exp ℝ)*(G*(a*Q))=PowerSeries.C (C*S)*(((PowerSeries.exp ℝ)^3)*g*a*e) := by
    dsimp [G,Q,E]
    ring
  rw [hmaj,PowerSeries.coeff_C_mul] at hProd
  rw [hser,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul,abs_mul]
  apply (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hProd) (abs_nonneg (2*A Y))).trans_eq
  dsimp only [S]
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),pow_succ]
  ring
lemma nonseparatingSeries_uniform_normalized_majorant : ∃ B M₀:ℝ,0<B ∧ 0<M₀ ∧
    ∀M:ℝ,M₀≤M→∀j:ℕ,∀Y∈Set.Icc (0:ℝ) y₀,∀F:HierarchyJet,∀e g a:Series,
      (∀n:ℕ,0≤PowerSeries.coeff n e)→(∀n:ℕ,0≤PowerSeries.coeff n g)→(∀n:ℕ,0≤PowerSeries.coeff n a)→
      (∀i:ℕ,i≤j→∀d:List ℕ,1≤d.length→|PowerSeries.coeff i (F.profile d)|≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)→
      (∀i:ℕ,i≤j→∀p:ℕ,1≤p→|PowerSeries.coeff i (F.cusp p)|≤
        (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i g)→
      (∀i:ℕ,i≤j→∀p:ℕ,1≤p→|PowerSeries.coeff i (F.genus p)|≤
        (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i a)→
      ∀t:ℕ,∀d:List ℕ,
      |PowerSeries.coeff (j+1) (nonseparatingSeries Y F t d)|≤
        B*(profileOrderWeight M (j+1) (t::d))^(2*j+1)*PowerSeries.coeff j (((PowerSeries.exp ℝ)^3)*g*a*e) := by
  obtain ⟨C,M₀,hC,hM₀,hdata⟩:=nonseparatingSeries_normalized_majorant
  obtain ⟨A₀,hA₀,hA⟩:=dilaton_A_abs_uniform
  refine ⟨2*C*A₀,M₀,by positivity,hM₀,?_⟩
  intro M hM j Y hY F e g a he hg ha hprofile hcusp hgenus t d
  have hi:=hdata M hM j Y hY F e g a he hg ha hprofile hcusp hgenus t d
  have hMpos:0<M:=lt_of_lt_of_le hM₀ hM
  have hS:0≤profileOrderWeight M (j+1) (t::d):=by unfold profileOrderWeight;positivity
  have hExp3:∀n:ℕ,0≤PowerSeries.coeff n ((PowerSeries.exp ℝ)^3):=by
    simpa only [pow_succ,pow_one,pow_zero,one_mul] using
      coeff_mul_nonneg (coeff_mul_nonneg exp_coeff_nonneg exp_coeff_nonneg) exp_coeff_nonneg
  have hTop:=coeff_mul_nonneg (coeff_mul_nonneg (coeff_mul_nonneg hExp3 hg) ha) he
  apply hi.trans
  have hb:=mul_le_mul_of_nonneg_right (hA Y hY)
    (mul_nonneg (mul_nonneg (by positivity : 0≤2*C) (pow_nonneg hS (2*j+1))) (hTop j))
  convert! hb using 1 <;>ring

end WP.HigherOrder
