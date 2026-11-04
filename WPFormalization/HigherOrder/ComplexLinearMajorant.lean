import WPFormalization.HigherOrder.ComplexHandleMajorant
import WPFormalization.HigherOrder.LinearProfileMajorant

/-! The genuine complex linear operators, summed along the actual fixed coordinate path. The remaining separating contribution is the exact original path sum of coefficient norms, not an assumed estimate. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries
lemma linearSeries_uniform_norm_majorant (ρ K A₀:ℝ) (hρ:1<ρ) (hK:0<K) (hA₀:0<A₀) : ∃ B M₀:ℝ,0<B ∧ 0<M₀ ∧
    ∀R:ℂ→ℂ,∀z:ℂ,(∀l:ℕ,‖WP.Analysis.complexWeightCoeff R l z‖≤K/ρ^l)→‖kernelA R z‖≤A₀→
    ∀M:ℝ,M₀≤M→∀j:ℕ,∀F:HierarchyJet,∀e g a:WP.HigherOrder.Series,
      (∀n:ℕ,0≤PowerSeries.coeff n e)→(∀n:ℕ,0≤PowerSeries.coeff n g)→(∀n:ℕ,0≤PowerSeries.coeff n a)→
      (∀i:ℕ,i≤j→∀d:List ℕ,1≤d.length→‖PowerSeries.coeff i (F.profile d)‖≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)→
      (∀i:ℕ,i≤j→∀p:ℕ,1≤p→‖PowerSeries.coeff i (F.cusp p)‖≤
        (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i g)→
      (∀i:ℕ,i≤j→∀p:ℕ,1≤p→‖PowerSeries.coeff i (F.genus p)‖≤
        (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i a)→
      ∀t:ℕ,∀d:List ℕ,
      ‖PowerSeries.coeff (j+1) (mergerSeries R z F t d+nonseparatingSeries R z F t d)‖≤
        B*(profileOrderWeight M (j+1) (t::d))^(2*j+1)*
          PowerSeries.coeff j (((PowerSeries.exp ℝ)^3)*g*(1+a)*e) := by
  obtain ⟨B₁,M₁,hB₁,hM₁,hm⟩:=mergerSeries_uniform_norm_majorant ρ K A₀ hρ hK hA₀
  obtain ⟨B₂,M₂,hB₂,hM₂,hn⟩:=nonseparatingSeries_uniform_norm_majorant ρ K A₀ hρ hK hA₀
  refine ⟨B₁+B₂,max M₁ M₂,by positivity,lt_of_lt_of_le hM₁ (le_max_left _ _),?_⟩
  intro R z hgeom hA M hM j F e g a he hg ha hprofile hcusp hgenus t d
  have hM1:M₁≤M:=(le_max_left _ _).trans hM
  have hM2:M₂≤M:=(le_max_right _ _).trans hM
  have hMm:0≤M:=(lt_of_lt_of_le hM₁ hM1).le
  let S:=profileOrderWeight M (j+1) (t::d)
  have hS:0≤S:=by dsimp[S,profileOrderWeight];positivity
  have hExp3:∀n:ℕ,0≤PowerSeries.coeff n ((PowerSeries.exp ℝ)^3):=by
    simpa only[pow_succ,pow_one,pow_zero,one_mul] using
      coeff_mul_nonneg (coeff_mul_nonneg exp_coeff_nonneg exp_coeff_nonneg) exp_coeff_nonneg
  have hU:=coeff_mul_nonneg (coeff_mul_nonneg hExp3 hg) he
  have hV:=coeff_mul_nonneg (coeff_mul_nonneg (coeff_mul_nonneg hExp3 hg) ha) he
  have hsum : ((PowerSeries.exp ℝ)^3)*g*(1+a)*e=
      ((PowerSeries.exp ℝ)^3)*g*e+((PowerSeries.exp ℝ)^3)*g*a*e:=by ring
  rw [map_add]
  calc _ ≤ ‖PowerSeries.coeff (j+1) (mergerSeries R z F t d)‖+
      ‖PowerSeries.coeff (j+1) (nonseparatingSeries R z F t d)‖:=norm_add_le _ _
    _ ≤ B₁*S^(2*j+1)*PowerSeries.coeff j (((PowerSeries.exp ℝ)^3)*g*e)+
        B₂*S^(2*j+1)*PowerSeries.coeff j (((PowerSeries.exp ℝ)^3)*g*a*e):=
      add_le_add (hm R z hgeom hA M hM1 j F e g he hg hprofile hcusp t d)
        (hn R z hgeom hA M hM2 j F e g a he hg ha hprofile hcusp hgenus t d)
    _ ≤ (B₁+B₂)*S^(2*j+1)*PowerSeries.coeff j (((PowerSeries.exp ℝ)^3)*g*e)+
        (B₁+B₂)*S^(2*j+1)*PowerSeries.coeff j (((PowerSeries.exp ℝ)^3)*g*a*e):=by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hS _)) (hU j)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hS _)) (hV j)
    _ = _ :=by rw[hsum,map_add];dsimp[S];ring


lemma profileAtOrder_norm_le_linear_plus_separating (ρ K A₀:ℝ) (hρ:1<ρ) (hK:0<K) (hA₀:0<A₀) : ∃ B M₀:ℝ,0<B ∧ 0<M₀ ∧
    ∀R:ℂ→ℂ,∀z:ℂ,(∀l:ℕ,‖WP.Analysis.complexWeightCoeff R l z‖≤K/ρ^l)→‖kernelA R z‖≤A₀→
    ∀M:ℝ,M₀≤M→∀j:ℕ,∀F:HierarchyJet,∀e g a:WP.HigherOrder.Series,
      (∀n:ℕ,0≤PowerSeries.coeff n e)→(∀n:ℕ,0≤PowerSeries.coeff n g)→(∀n:ℕ,0≤PowerSeries.coeff n a)→
      (∀i:ℕ,i≤j→∀d:List ℕ,1≤d.length→‖PowerSeries.coeff i (F.profile d)‖≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)→
      (∀i:ℕ,i≤j→∀p:ℕ,1≤p→‖PowerSeries.coeff i (F.cusp p)‖≤
        (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i g)→
      (∀i:ℕ,i≤j→∀p:ℕ,1≤p→‖PowerSeries.coeff i (F.genus p)‖≤
        (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i a)→
      ∀P:PsiTheory,∀d:List ℕ,
      ‖profileAtOrder P R z F (j+1) d‖≤
        B*(profileOrderWeight M (j+1) d)^(2*j+2)*
          PowerSeries.coeff j (((PowerSeries.exp ℝ)^3)*g*(1+a)*e)+
        ∑i∈Finset.range d.length,∑t∈Finset.range d[i]!,
          ‖PowerSeries.coeff (j+1) (separatingSeries P R z F (j+1)
            ((beforeCoordinate d i t)[i]!) ((beforeCoordinate d i t).eraseIdx i))‖ := by
  obtain ⟨B,M₀,hB,hM₀,hlinear⟩:=linearSeries_uniform_norm_majorant ρ K A₀ hρ hK hA₀
  refine ⟨B,M₀,hB,hM₀,?_⟩
  intro R z hgeom hA M hM j F e g a he hg ha hprofile hcusp hgenus P d
  have hM0:0≤M:=(lt_of_lt_of_le hM₀ hM).le
  let S:=profileOrderWeight M (j+1) d
  let Q:=PowerSeries.coeff j (((PowerSeries.exp ℝ)^3)*g*(1+a)*e)
  have hS:0≤S:=by dsimp[S,profileOrderWeight];positivity
  have hExp3:∀n:ℕ,0≤PowerSeries.coeff n ((PowerSeries.exp ℝ)^3):=by
    simpa only[pow_succ,pow_one,pow_zero,one_mul] using
      coeff_mul_nonneg (coeff_mul_nonneg exp_coeff_nonneg exp_coeff_nonneg) exp_coeff_nonneg
  have h1a:∀n:ℕ,0≤PowerSeries.coeff n (1+a):=by
    intro n
    rw[map_add]
    exact add_nonneg (by rw[PowerSeries.coeff_one];split_ifs<;>norm_num) (ha n)
  have hQ:0≤Q:=coeff_mul_nonneg (coeff_mul_nonneg (coeff_mul_nonneg hExp3 hg) h1a) he j
  have hterm (i:ℕ) (hi:i∈Finset.range d.length) (t:ℕ) (ht:t∈Finset.range d[i]!) :
      ‖adjacentCoefficient P R z F (j+1) i (beforeCoordinate d i t)‖≤
        B*S^(2*j+1)*Q+
          ‖PowerSeries.coeff (j+1) (separatingSeries P R z F (j+1)
            ((beforeCoordinate d i t)[i]!) ((beforeCoordinate d i t).eraseIdx i))‖ := by
    let v:=beforeCoordinate d i t
    have hiv:i<v.length:=by simpa only[v,beforeCoordinate_length] using Finset.mem_range.mp hi
    have hlin:=hlinear R z hgeom hA M hM j F e g a he hg ha hprofile hcusp hgenus (v[i]!) (v.eraseIdx i)
    rw[coordinate_parent_order_weight M (j+1) v i hiv] at hlin
    have hvs:(v.sum:ℝ)≤d.sum:=by exact_mod_cast beforeCoordinate_sum_le d i t (Finset.mem_range.mp hi) (Finset.mem_range.mp ht).le
    have hvw:profileOrderWeight M (j+1) v≤S:=by
      dsimp only[profileOrderWeight,S]
      rw[show v.length=d.length from beforeCoordinate_length d i t]
      linarith
    have hvw0:0≤profileOrderWeight M (j+1) v:=by unfold profileOrderWeight;positivity
    have hlin':‖PowerSeries.coeff (j+1) (mergerSeries R z F (v[i]!) (v.eraseIdx i)+
        nonseparatingSeries R z F (v[i]!) (v.eraseIdx i))‖≤B*S^(2*j+1)*Q:=
      hlin.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hvw0 hvw _) hB.le) hQ)
    dsimp only[adjacentCoefficient]
    rw[norm_neg,map_add]
    exact (norm_add_le _ _).trans (add_le_add_left hlin' _)
  have hlookup:(∑i∈Finset.range d.length,(d[i]!:ℝ))=(d.sum:ℝ):=by
    rw[sum_range_getElem]
    exact (map_list_sum (Nat.castAddMonoidHom ℝ) d).symm
  calc ‖profileAtOrder P R z F (j+1) d‖
      ≤ ∑i∈Finset.range d.length,∑t∈Finset.range d[i]!,
          ‖adjacentCoefficient P R z F (j+1) i (beforeCoordinate d i t)‖:=by
        unfold profileAtOrder
        exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum (fun i hi=>norm_sum_le _ _))
    _ ≤ ∑i∈Finset.range d.length,∑t∈Finset.range d[i]!,
        (B*S^(2*j+1)*Q+‖PowerSeries.coeff (j+1) (separatingSeries P R z F (j+1)
          ((beforeCoordinate d i t)[i]!) ((beforeCoordinate d i t).eraseIdx i))‖):=
        Finset.sum_le_sum (fun i hi=>Finset.sum_le_sum (fun t ht=>hterm i hi t ht))
    _ = (d.sum:ℝ)*(B*S^(2*j+1)*Q)+
        ∑i∈Finset.range d.length,∑t∈Finset.range d[i]!,
          ‖PowerSeries.coeff (j+1) (separatingSeries P R z F (j+1)
            ((beforeCoordinate d i t)[i]!) ((beforeCoordinate d i t).eraseIdx i))‖ :=by
        simp only[Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        rw[←Finset.sum_mul,hlookup]
    _ ≤ _ :=by
      apply add_le_add_left
      have hh:=mul_le_mul_of_nonneg_right
        (canonical_path_count_le_order_weight M hM0 (j+1) d)
        (mul_nonneg (mul_nonneg hB.le (pow_nonneg hS (2*j+1))) hQ)
      convert! hh using 1 <;>dsimp[S,Q]<;>simp only[show 2*j+2=(2*j+1)+1 by omega,pow_succ]<;>ring


end WP.HigherOrder.ComplexCanonical
