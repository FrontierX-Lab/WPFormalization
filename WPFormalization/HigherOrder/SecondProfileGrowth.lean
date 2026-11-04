import WPFormalization.HigherOrder.SecondProfile
import WPFormalization.HigherOrder.Coherence
import WPFormalization.Marked.FirstDegreeLarge
import WPFormalization.Marked.GenusSecondOrderAll
import WPFormalization.Analysis.KernelPolynomialTails
import WPFormalization.Analysis.ThetaNonnegative
/-! Canonical second degree coefficients: genuine absolute kernel summability
and uniform cubic increment / quartic profile growth from the original definitions.
The finite canonical coordinate path is bounded by the parent total degree. -/
noncomputable section
open Set
namespace WP.HigherOrder
lemma transportBeta_abs_uniform (p : ℕ) : ∃ C : ℝ,0 < C ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, |transportBeta p Y| ≤ C := by
  obtain ⟨a,ha,hA⟩ := singleMarking_A_uniform_lower
  obtain ⟨K,hK,hβ⟩ := dilaton_correction_abs_uniform p
  refine ⟨K/a,by positivity,?_⟩
  intro Y hY
  apply (le_div_iff₀ ha).2
  have hAY : 0 < A Y := ha.trans_le (hA Y hY)
  have hi := hβ Y hY
  have hb : |A Y*transportBeta p Y| ≤ K := by simpa only [transportBeta,dilatonBeta] using hi
  rw [abs_mul,abs_of_pos hAY] at hb
  calc _ ≤ |transportBeta p Y| * A Y := mul_le_mul_of_nonneg_left (hA Y hY) (abs_nonneg _)
       _ ≤ K := by nlinarith
lemma tailWeight_nonneg_le_Theta (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) (j : ℕ) :
    0 ≤ tailWeight Y j ∧ tailWeight Y j ≤ Theta Y := by
  have hs := (Analysis.weight_hasSum_at_one Y hY).summable
  have he := hs.sum_add_tsum_nat_add j
  have hp : 0 ≤ ∑ i ∈ Finset.range j,weight Y i := Finset.sum_nonneg (fun i hi=>weight_nonneg Y hY i)
  refine ⟨tsum_nonneg (fun i=>weight_nonneg Y hY (i+j)),?_⟩
  change (∑'i:ℕ,weight Y (i+j)) ≤ ∑'i:ℕ,weight Y i
  linarith
lemma canonical_weighted_polynomial_bound (q : ℕ) : ∃ M : ℝ,0 < M ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, ∀ D : ℕ, ∀ K : ℝ,0 ≤ K → ∀ f : ℕ→ℝ,
      (∀ l,|f l| ≤ K*((D:ℝ)+l+1)^q) →
      Summable (fun l=>weight Y l*f l) ∧
        |∑'l:ℕ,weight Y l*f l| ≤ K*M*((D:ℝ)+1)^q := by
  obtain ⟨M,hM,hpoly⟩ := Analysis.weight_polynomial_tail_uniform q 0
  refine ⟨M,hM,?_⟩
  intro Y hY D K hK f hf
  have hp := hpoly Y hY D 0
  simp only [Nat.zero_le,ite_true,pow_zero,div_one] at hp
  have hmajor := hp.1.mul_left K
  have hpoint (l : ℕ) : |weight Y l*f l| ≤ K*(((D:ℝ)+l+1)^q*weight Y l) := by
    rw [abs_mul,abs_of_nonneg (weight_nonneg Y hY l)]
    have hi := mul_le_mul_of_nonneg_left (hf l) (weight_nonneg Y hY l)
    nlinarith [hi]
  have hn : Summable (fun l=>|weight Y l*f l|) :=
    Summable.of_nonneg_of_le (fun l=>abs_nonneg _) hpoint hmajor
  have hs : Summable (fun l=>weight Y l*f l) := Summable.of_norm (by simpa only [Real.norm_eq_abs] using hn)
  refine ⟨hs,?_⟩
  calc _ ≤ ∑'l:ℕ,|weight Y l*f l| := by
         simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
           (show Summable (fun l=>‖weight Y l*f l‖) by simpa only [Real.norm_eq_abs] using hn)
       _ ≤ ∑'l:ℕ,K*(((D:ℝ)+l+1)^q*weight Y l) := hn.tsum_le_tsum hpoint hmajor
       _ = K*∑'l:ℕ,((D:ℝ)+l+1)^q*weight Y l := tsum_mul_left
       _ ≤ K*(M*((D:ℝ)+1)^q) := mul_le_mul_of_nonneg_left hp.2 hK
       _ = _ := by ring
lemma sum_eraseIdx_component (d : List ℕ) (i : ℕ) (hi : i<d.length) :
    d[i]!+(d.eraseIdx i).sum=d.sum ∧ (d.eraseIdx i).length+1=d.length := by
  have hget : d[i] = d[i]! := by simp [hi]
  have hp := List.getElem_cons_eraseIdx_perm hi
  rw [hget] at hp
  exact ⟨by simpa using hp.sum_eq,by simpa using hp.length_eq⟩
lemma beforeCoordinate_sum_le (d : List ℕ) (i t : ℕ) (hi : i<d.length) (ht : t ≤ d[i]!) :
    (beforeCoordinate d i t).sum ≤ d.sum := by
  have hlookup : (∑j:Fin d.length,d[j.val]!)=d.sum := by
    rw [←List.sum_ofFn]
    have he : (fun j:Fin d.length=>d[j.val]!)=(fun j:Fin d.length=>d[j.val]) := by
      funext j
      simp [j.isLt]
    rw [he,List.ofFn_getElem]
  rw [beforeCoordinate,List.sum_ofFn,←hlookup]
  apply Finset.sum_le_sum
  intro j hj
  split_ifs with hji hje
  · exact le_rfl
  · simpa only [hje] using ht
  · exact Nat.zero_le _

lemma merger_child_length_sum (d : List ℕ) (i j l : ℕ) (hi : i<d.length)
    (hj : j<(d.eraseIdx i).length) :
    ((d[i]!+(d.eraseIdx i)[j]!+l-1)::(d.eraseIdx i).eraseIdx j).length=d.length-1 ∧
    ((d[i]!+(d.eraseIdx i)[j]!+l-1)::(d.eraseIdx i).eraseIdx j).sum ≤ d.sum+l := by
  obtain ⟨hs,hl⟩ := sum_eraseIdx_component d i hi
  obtain ⟨hs',hl'⟩ := sum_eraseIdx_component (d.eraseIdx i) j hj
  simp only [List.length_cons,List.sum_cons]
  constructor <;> omega
lemma handle_child_length_sum (d : List ℕ) (i l u : ℕ) (hi : i<d.length)
    (hu : u<d[i]!+l-1) :
    (u::(d[i]!+l-2-u)::d.eraseIdx i).length=d.length+1 ∧
    (u::(d[i]!+l-2-u)::d.eraseIdx i).sum ≤ d.sum+l := by
  obtain ⟨hs,hl⟩ := sum_eraseIdx_component d i hi
  simp only [List.length_cons,List.sum_cons]
  constructor <;> omega
lemma center_minus_quadratic_bound (v z s B C : ℝ) (hs : 1 ≤ s)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hv : |v| ≤ B) (hz : |z| ≤ C*s^2) :
    |v-z| ≤ (B+C)*s^2 := by
  have hs2 : 1 ≤ s^2 := by nlinarith
  calc _ ≤ |v|+|z| := abs_sub _ _
       _ ≤ B+C*s^2 := add_le_add hv hz
       _ ≤ (B+C)*s^2 := by nlinarith [mul_le_mul_of_nonneg_left hs2 hB]

lemma second_merger_inner_abs_uniform (p : ℕ) : ∃ C : ℝ,0 < C ∧
    ∀ d : List ℕ,d.length=p → ∀ i : ℕ,i<d.length → ∀ j : ℕ,j<(d.eraseIdx i).length →
    ∀ Y ∈ Icc (0:ℝ) y₀,
      Summable (fun l : ℕ => if 1 ≤ d[i]!+(d.eraseIdx i)[j]!+l then
        weight Y l*(1-transportBeta (p-1) Y-
          degreeCorrection ((d[i]!+(d.eraseIdx i)[j]!+l-1)::(d.eraseIdx i).eraseIdx j) Y) else 0) ∧
      |∑'l:ℕ,if 1 ≤ d[i]!+(d.eraseIdx i)[j]!+l then
        weight Y l*(1-transportBeta (p-1) Y-
          degreeCorrection ((d[i]!+(d.eraseIdx i)[j]!+l-1)::(d.eraseIdx i).eraseIdx j) Y) else 0| ≤
        C*((d.sum:ℝ)+1)^2 := by
  obtain ⟨B,hB,hβ⟩ := transportBeta_abs_uniform (p-1)
  obtain ⟨Q,hQ,hδ⟩ := degreeCorrection_uniform_quadratic_bound (p-1)
  obtain ⟨M,hM,hweight⟩ := canonical_weighted_polynomial_bound 2
  let K : ℝ := 1+B+Q
  have hK : 0 < K := by dsimp only [K];positivity
  refine ⟨K*M,by positivity,?_⟩
  intro d hd i hi j hj Y hY
  let f := fun l : ℕ => if 1 ≤ d[i]!+(d.eraseIdx i)[j]!+l then
    1-transportBeta (p-1) Y-degreeCorrection ((d[i]!+(d.eraseIdx i)[j]!+l-1)::(d.eraseIdx i).eraseIdx j) Y else 0
  have hpoint (l : ℕ) : |f l| ≤ K*((d.sum:ℝ)+l+1)^2 := by
    have hs : 1 ≤ (d.sum:ℝ)+l+1 := by linarith [Nat.cast_nonneg (α:=ℝ) d.sum,Nat.cast_nonneg (α:=ℝ) l]
    dsimp only [f]
    split_ifs
    · have hchild := merger_child_length_sum d i j l hi hj
      have hδ' := hδ _ (by simpa only [hd] using hchild.1) Y hY
      have hsum : (((d[i]!+(d.eraseIdx i)[j]!+l-1)::(d.eraseIdx i).eraseIdx j).sum:ℝ)+1 ≤ (d.sum:ℝ)+l+1 := by
        exact_mod_cast Nat.succ_le_succ hchild.2
      have hδlarge := hδ'.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hsum 2) hQ.le)
      have hcenter : |1-transportBeta (p-1) Y| ≤ 1+B :=
        (abs_sub _ _).trans (by simpa only [abs_one] using add_le_add_right (hβ Y hY) (1:ℝ))
      exact center_minus_quadratic_bound _ _ _ (1+B) Q hs (by positivity) hQ.le hcenter hδlarge
    · simp only [abs_zero]
      positivity
  obtain ⟨hs,hb⟩ := hweight Y hY d.sum K hK.le f hpoint
  have he : (fun l : ℕ => weight Y l*f l)=(fun l : ℕ => if 1 ≤ d[i]!+(d.eraseIdx i)[j]!+l then
      weight Y l*(1-transportBeta (p-1) Y-
        degreeCorrection ((d[i]!+(d.eraseIdx i)[j]!+l-1)::(d.eraseIdx i).eraseIdx j) Y) else 0) := by
    funext l
    dsimp only [f]
    split_ifs <;> simp
  rw [he] at hs hb
  exact ⟨hs,hb⟩
lemma second_handle_inner_abs_uniform (p : ℕ) : ∃ C : ℝ,0 < C ∧
    ∀ d : List ℕ,d.length=p → ∀ i : ℕ,i<d.length → ∀ Y ∈ Icc (0:ℝ) y₀,
      Summable (fun l : ℕ => if 2 ≤ d[i]!+l then weight Y l*
        ∑u ∈ Finset.range (d[i]!+l-1),
          (1-transportBeta (p+1) Y-alpha p Y-degreeCorrection (u::(d[i]!+l-2-u)::d.eraseIdx i) Y) else 0) ∧
      |∑'l:ℕ,if 2 ≤ d[i]!+l then weight Y l*
        ∑u ∈ Finset.range (d[i]!+l-1),
          (1-transportBeta (p+1) Y-alpha p Y-degreeCorrection (u::(d[i]!+l-2-u)::d.eraseIdx i) Y) else 0| ≤
        C*((d.sum:ℝ)+1)^3 := by
  obtain ⟨B,hB,hβ⟩ := transportBeta_abs_uniform (p+1)
  obtain ⟨D,hD,hα⟩ := genus_second_alpha_abs_uniform p
  obtain ⟨Q,hQ,hδ⟩ := degreeCorrection_uniform_quadratic_bound (p+1)
  obtain ⟨M,hM,hweight⟩ := canonical_weighted_polynomial_bound 3
  let K : ℝ := 1+B+D+Q
  have hK : 0 < K := by dsimp only [K];positivity
  refine ⟨K*M,by positivity,?_⟩
  intro d hd i hi Y hY
  let f := fun l : ℕ => if 2 ≤ d[i]!+l then
    ∑u ∈ Finset.range (d[i]!+l-1),
      (1-transportBeta (p+1) Y-alpha p Y-degreeCorrection (u::(d[i]!+l-2-u)::d.eraseIdx i) Y) else 0
  have hpoint (l : ℕ) : |f l| ≤ K*((d.sum:ℝ)+l+1)^3 := by
    have hs : 1 ≤ (d.sum:ℝ)+l+1 := by linarith [Nat.cast_nonneg (α:=ℝ) d.sum,Nat.cast_nonneg (α:=ℝ) l]
    dsimp only [f]
    split_ifs
    · have hterm (u : ℕ) (hu : u ∈ Finset.range (d[i]!+l-1)) :
          |1-transportBeta (p+1) Y-alpha p Y-degreeCorrection (u::(d[i]!+l-2-u)::d.eraseIdx i) Y| ≤
            K*((d.sum:ℝ)+l+1)^2 := by
        have hchild := handle_child_length_sum d i l u hi (Finset.mem_range.mp hu)
        have hδ' := hδ _ (by simpa only [hd] using hchild.1) Y hY
        have hsum : ((u::(d[i]!+l-2-u)::d.eraseIdx i).sum:ℝ)+1 ≤ (d.sum:ℝ)+l+1 := by
          exact_mod_cast Nat.succ_le_succ hchild.2
        have hδlarge := hδ'.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hsum 2) hQ.le)
        have hβcenter : |1-transportBeta (p+1) Y| ≤ 1+B :=
          (abs_sub _ _).trans (by simpa only [abs_one] using add_le_add_right (hβ Y hY) (1:ℝ))
        have hcenter : |1-transportBeta (p+1) Y-alpha p Y| ≤ 1+B+D :=
          (abs_sub _ _).trans (add_le_add hβcenter (hα Y hY))
        exact center_minus_quadratic_bound _ _ _ (1+B+D) Q hs (by positivity) hQ.le hcenter hδlarge
      have hcount : ((d[i]!+l-1:ℕ):ℝ) ≤ (d.sum:ℝ)+l+1 := by
        have ht := sum_eraseIdx_component d i hi
        exact_mod_cast (show d[i]!+l-1 ≤ d.sum+l+1 by omega)
      calc _ ≤ ∑u ∈ Finset.range (d[i]!+l-1),
            |1-transportBeta (p+1) Y-alpha p Y-degreeCorrection (u::(d[i]!+l-2-u)::d.eraseIdx i) Y| :=
              Finset.abs_sum_le_sum_abs _ _
           _ ≤ ∑u ∈ Finset.range (d[i]!+l-1),K*((d.sum:ℝ)+l+1)^2 := Finset.sum_le_sum hterm
           _ = ((d[i]!+l-1:ℕ):ℝ)*(K*((d.sum:ℝ)+l+1)^2) := by simp [nsmul_eq_mul]
           _ ≤ ((d.sum:ℝ)+l+1)*(K*((d.sum:ℝ)+l+1)^2) :=
             mul_le_mul_of_nonneg_right hcount (by positivity)
           _ = _ := by ring
    · simp only [abs_zero]
      positivity
  obtain ⟨hs,hb⟩ := hweight Y hY d.sum K hK.le f hpoint
  have he : (fun l : ℕ => weight Y l*f l)=(fun l : ℕ => if 2 ≤ d[i]!+l then weight Y l*
      ∑u ∈ Finset.range (d[i]!+l-1),
        (1-transportBeta (p+1) Y-alpha p Y-degreeCorrection (u::(d[i]!+l-2-u)::d.eraseIdx i) Y) else 0) := by
    funext l
    dsimp only [f]
    split_ifs <;> simp
  rw [he] at hs hb
  exact ⟨hs,hb⟩

lemma second_tail_abs_uniform (p : ℕ) : ∃ C : ℝ,0 < C ∧
    ∀ d : List ℕ,d.length ≤ p → ∀ t : ℕ,∀ Y ∈ Icc (0:ℝ) y₀,
      |(A Y)^2*((((Nat.choose (zeros d) 2:ℕ):ℝ)+theta Y 1/2)*tailWeight Y (2-t)+
        tailWeight Y (3-t)/2)| ≤ C := by
  obtain ⟨B,hB,hA⟩ := dilaton_A_abs_uniform
  obtain ⟨M,hM,hΘ⟩ := dilaton_weight_moments_abs_uniform
  obtain ⟨T,hθ⟩ := uniform_kernel_moments.1
  let Q : ℝ := max 1 T
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let C : ℝ := B^2*(((p:ℝ)^2+Q/2)*M+M/2)+1
  have hC : 0 < C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro d hd t Y hY
  have ht₁ := tailWeight_nonneg_le_Theta Y hY (2-t)
  have ht₂ := tailWeight_nonneg_le_Theta Y hY (3-t)
  have hT : Theta Y ≤ M := (le_abs_self _).trans (hΘ Y hY).1
  have ht₁M := ht₁.2.trans hT
  have ht₂M := ht₂.2.trans hT
  have hθ0 := theta_nonneg Y hY 1
  have hθQ : theta Y 1 ≤ Q := ((hθ Y hY).2.2 1).1.trans (le_max_right _ _)
  have hz : zeros d ≤ p := by have := zeros_add_positiveCount d;omega
  have hzR : (zeros d:ℝ) ≤ p := by exact_mod_cast hz
  have hchoose : ((Nat.choose (zeros d) 2:ℕ):ℝ) ≤ (p:ℝ)^2 := by
    have hc : ((Nat.choose (zeros d) 2:ℕ):ℝ) ≤ (zeros d:ℝ)^2 := by
      exact_mod_cast Nat.choose_le_pow (zeros d) 2
    exact hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hzR 2)
  have hchoose0 : 0 ≤ ((Nat.choose (zeros d) 2:ℕ):ℝ) := Nat.cast_nonneg _
  have hcoef0 : 0 ≤ ((Nat.choose (zeros d) 2:ℕ):ℝ)+theta Y 1/2 := by positivity
  have hcoef : ((Nat.choose (zeros d) 2:ℕ):ℝ)+theta Y 1/2 ≤ (p:ℝ)^2+Q/2 := by linarith
  have hinner0 : 0 ≤ ((((Nat.choose (zeros d) 2:ℕ):ℝ)+theta Y 1/2)*tailWeight Y (2-t)+tailWeight Y (3-t)/2) :=
    add_nonneg (mul_nonneg hcoef0 ht₁.1) (div_nonneg ht₂.1 (by norm_num))
  have hinner : ((((Nat.choose (zeros d) 2:ℕ):ℝ)+theta Y 1/2)*tailWeight Y (2-t)+tailWeight Y (3-t)/2) ≤
      ((p:ℝ)^2+Q/2)*M+M/2 :=
    add_le_add (mul_le_mul hcoef ht₁M ht₁.1 (by positivity))
      (div_le_div_of_nonneg_right ht₂M (by norm_num))
  have hA2 : (A Y)^2 ≤ B^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hA Y hY) 2
  rw [abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_nonneg hinner0]
  exact (mul_le_mul hA2 hinner hinner0 (sq_nonneg B)).trans (by dsimp only [C];linarith)

lemma second_merger_outer_abs_uniform (p : ℕ) : ∃ C : ℝ,0 < C ∧
    ∀ d : List ℕ,d.length=p → ∀ i : ℕ,i<d.length → ∀ Y ∈ Icc (0:ℝ) y₀,
      |A Y*(∑ j ∈ Finset.range (d.eraseIdx i).length,(2*((d.eraseIdx i)[j]!:ℝ)+1)*
        ∑'l:ℕ,if 1 ≤ d[i]!+(d.eraseIdx i)[j]!+l then
          weight Y l*(1-transportBeta (p-1) Y-
            degreeCorrection ((d[i]!+(d.eraseIdx i)[j]!+l-1)::(d.eraseIdx i).eraseIdx j) Y) else 0)| ≤
        C*((d.sum:ℝ)+1)^3 := by
  obtain ⟨B,hB,hA⟩ := dilaton_A_abs_uniform
  obtain ⟨M,hM,hinner⟩ := second_merger_inner_abs_uniform p
  refine ⟨2*B*((p:ℝ)+1)*M,by positivity,?_⟩
  intro d hd i hi Y hY
  let F := fun j : ℕ => ∑'l:ℕ,if 1 ≤ d[i]!+(d.eraseIdx i)[j]!+l then
    weight Y l*(1-transportBeta (p-1) Y-
      degreeCorrection ((d[i]!+(d.eraseIdx i)[j]!+l-1)::(d.eraseIdx i).eraseIdx j) Y) else 0
  have hsum : |∑ j ∈ Finset.range (d.eraseIdx i).length,(2*((d.eraseIdx i)[j]!:ℝ)+1)*F j| ≤
      (2*((p:ℝ)+1)*M)*((d.sum:ℝ)+1)^3 := by
    have hterm (j : ℕ) (hj : j ∈ Finset.range (d.eraseIdx i).length) :
        |(2*((d.eraseIdx i)[j]!:ℝ)+1)*F j| ≤
          (2*((d.sum:ℝ)+1))*(M*((d.sum:ℝ)+1)^2) := by
      have hs := sum_eraseIdx_component d i hi
      have ht := sum_eraseIdx_component (d.eraseIdx i) j (Finset.mem_range.mp hj)
      have hjNat : (d.eraseIdx i)[j]! ≤ d.sum := by omega
      have hjR : ((d.eraseIdx i)[j]!:ℝ) ≤ d.sum := by exact_mod_cast hjNat
      have hc0 : 0 ≤ 2*((d.eraseIdx i)[j]!:ℝ)+1 := by positivity
      have hc : 2*((d.eraseIdx i)[j]!:ℝ)+1 ≤ 2*((d.sum:ℝ)+1) := by linarith
      have hb := (hinner d hd i hi j (Finset.mem_range.mp hj) Y hY).2
      rw [abs_mul,abs_of_nonneg hc0]
      exact mul_le_mul hc hb (abs_nonneg _) (by positivity)
    calc _ ≤ ∑j ∈ Finset.range (d.eraseIdx i).length,|(2*((d.eraseIdx i)[j]!:ℝ)+1)*F j| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑j ∈ Finset.range (d.eraseIdx i).length,(2*((d.sum:ℝ)+1))*(M*((d.sum:ℝ)+1)^2) := Finset.sum_le_sum hterm
         _ = ((d.eraseIdx i).length:ℝ)*((2*((d.sum:ℝ)+1))*(M*((d.sum:ℝ)+1)^2)) := by simp [nsmul_eq_mul]
         _ ≤ ((p:ℝ)+1)*((2*((d.sum:ℝ)+1))*(M*((d.sum:ℝ)+1)^2)) := by
           apply mul_le_mul_of_nonneg_right _ (by positivity)
           have hh := (sum_eraseIdx_component d i hi).2
           exact_mod_cast (show (d.eraseIdx i).length ≤ p+1 by omega)
         _ = _ := by ring
  rw [abs_mul]
  have he := mul_le_mul (hA Y hY) hsum (abs_nonneg _) hB.le
  convert he using 1 <;> ring

lemma secondIncrement_abs_uniform (p : ℕ) (hp : 1 ≤ p) : ∃ C : ℝ,0 < C ∧
    ∀ d : List ℕ,d.length=p → ∀ i : ℕ,i<d.length → ∀ Y ∈ Icc (0:ℝ) y₀,
      |secondIncrement Y i d| ≤ C*((d.sum:ℝ)+1)^3 := by
  obtain ⟨Cm,hCm,hmerger⟩ := second_merger_outer_abs_uniform p
  obtain ⟨Ch,hCh,hhandle⟩ := second_handle_inner_abs_uniform p
  obtain ⟨Ct,hCt,htail⟩ := second_tail_abs_uniform p
  obtain ⟨B,hB,hA⟩ := dilaton_A_abs_uniform
  refine ⟨Cm+2*B*Ch+Ct,by positivity,?_⟩
  intro d hd i hi Y hY
  let M := ∑ j ∈ Finset.range (d.eraseIdx i).length,(2*((d.eraseIdx i)[j]!:ℝ)+1)*
    ∑'l:ℕ,if 1 ≤ d[i]!+(d.eraseIdx i)[j]!+l then
      weight Y l*(1-transportBeta (p-1) Y-
        degreeCorrection ((d[i]!+(d.eraseIdx i)[j]!+l-1)::(d.eraseIdx i).eraseIdx j) Y) else 0
  let H := ∑'l:ℕ,if 2 ≤ d[i]!+l then weight Y l*
    ∑u ∈ Finset.range (d[i]!+l-1),
      (1-transportBeta (p+1) Y-alpha p Y-degreeCorrection (u::(d[i]!+l-2-u)::d.eraseIdx i) Y) else 0
  let T := (A Y)^2*((((Nat.choose (zeros (d.eraseIdx i)) 2:ℕ):ℝ)+theta Y 1/2)*tailWeight Y (2-d[i]!)+
    tailWeight Y (3-d[i]!)/2)
  have hMC : |A Y*M| ≤ Cm*((d.sum:ℝ)+1)^3 := hmerger d hd i hi Y hY
  have hH0 : |H| ≤ Ch*((d.sum:ℝ)+1)^3 := (hhandle d hd i hi Y hY).2
  have h2A : |2*A Y| ≤ 2*B := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul_of_nonneg_left (hA Y hY) (by norm_num)
  have hHC : |2*A Y*H| ≤ (2*B*Ch)*((d.sum:ℝ)+1)^3 := by
    rw [abs_mul]
    have he := mul_le_mul h2A hH0 (abs_nonneg H) (by positivity)
    convert he using 1 <;> ring
  have hTC0 : |T| ≤ Ct := htail (d.eraseIdx i) (by
    have hh := (sum_eraseIdx_component d i hi).2
    omega) d[i]! Y hY
  have hs : 1 ≤ ((d.sum:ℝ)+1)^3 := by
    have hi := pow_le_pow_left₀ (show (0:ℝ) ≤ 1 by norm_num)
      (show (1:ℝ) ≤ (d.sum:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d.sum]) 3
    simpa only [one_pow] using hi
  have hTC : |T| ≤ Ct*((d.sum:ℝ)+1)^3 := hTC0.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hCt.le)
  simp only [secondIncrement,hd]
  change |A Y*M+2*A Y*H+T| ≤ (Cm+2*B*Ch+Ct)*((d.sum:ℝ)+1)^3
  calc _ ≤ (|A Y*M|+|2*A Y*H|)+|T| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
       _ ≤ (Cm*((d.sum:ℝ)+1)^3+(2*B*Ch)*((d.sum:ℝ)+1)^3)+Ct*((d.sum:ℝ)+1)^3 :=
         add_le_add (add_le_add hMC hHC) hTC
       _ = _ := by ring
lemma secondProfile_abs_uniform (p : ℕ) (hp : 1 ≤ p) : ∃ C : ℝ,0 < C ∧
    ∀ d : List ℕ,d.length=p → ∀ Y ∈ Icc (0:ℝ) y₀,
      |secondProfile Y d| ≤ C*((d.sum:ℝ)+1)^4 := by
  obtain ⟨C,hC,hinc⟩ := secondIncrement_abs_uniform p hp
  refine ⟨C,hC,?_⟩
  intro d hd Y hY
  have hterm (i : ℕ) (hi : i ∈ Finset.range d.length) (t : ℕ) (ht : t ∈ Finset.range d[i]!) :
      |secondIncrement Y i (beforeCoordinate d i t)| ≤ C*((d.sum:ℝ)+1)^3 := by
    have hi' := Finset.mem_range.mp hi
    have ht' := Finset.mem_range.mp ht
    have hb := hinc (beforeCoordinate d i t) (by simpa only [beforeCoordinate_length] using hd)
      i (by simpa only [beforeCoordinate_length] using hi') Y hY
    have hs := beforeCoordinate_sum_le d i t hi' ht'.le
    have hsR : ((beforeCoordinate d i t).sum:ℝ)+1 ≤ (d.sum:ℝ)+1 := by
      exact_mod_cast Nat.succ_le_succ hs
    exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsR 3) hC.le)
  have hlookup : (∑i ∈ Finset.range d.length,(d[i]!:ℝ))=(d.sum:ℝ) := by
    rw [sum_range_getElem]
    exact (map_list_sum (Nat.castAddMonoidHom ℝ) d).symm
  rw [secondProfile,abs_neg]
  calc _ ≤ ∑i ∈ Finset.range d.length,|∑t ∈ Finset.range d[i]!,secondIncrement Y i (beforeCoordinate d i t)| :=
          Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑i ∈ Finset.range d.length,∑t ∈ Finset.range d[i]!,|secondIncrement Y i (beforeCoordinate d i t)| :=
         Finset.sum_le_sum (fun i hi=>Finset.abs_sum_le_sum_abs _ _)
       _ ≤ ∑i ∈ Finset.range d.length,∑t ∈ Finset.range d[i]!,C*((d.sum:ℝ)+1)^3 :=
         Finset.sum_le_sum (fun i hi=>Finset.sum_le_sum (fun t ht=>hterm i hi t ht))
       _ = (∑i ∈ Finset.range d.length,(d[i]!:ℝ))*(C*((d.sum:ℝ)+1)^3) := by
         simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
         rw [Finset.sum_mul]
       _ = (d.sum:ℝ)*(C*((d.sum:ℝ)+1)^3) := by rw [hlookup]
       _ ≤ C*((d.sum:ℝ)+1)^4 := by
         have he := mul_le_mul_of_nonneg_right (show (d.sum:ℝ) ≤ (d.sum:ℝ)+1 by linarith)
           (show 0 ≤ C*((d.sum:ℝ)+1)^3 by positivity)
         convert he using 1 <;> ring

lemma second_merger_front_summable (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀)
    (t : ℕ) (d : List ℕ) (j : ℕ) (hj : j<d.length) :
    Summable (fun l : ℕ => if 1 ≤ t+d[j]!+l then weight Y l*
      (1-transportBeta d.length Y-degreeCorrection ((t+d[j]!+l-1)::d.eraseIdx j) Y) else 0) := by
  obtain ⟨C,hC,hbound⟩ := second_merger_inner_abs_uniform (d.length+1)
  have hs := (hbound (t::d) rfl 0 (by simp) j (by simpa using hj) Y hY).1
  simpa [List.eraseIdx] using hs
lemma second_handle_front_summable (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀)
    (t : ℕ) (d : List ℕ) :
    Summable (fun l : ℕ => if 2 ≤ t+l then weight Y l*
      ∑u ∈ Finset.range (t+l-1),
        (1-transportBeta (d.length+2) Y-alpha (d.length+1) Y-
          degreeCorrection (u::(t+l-2-u)::d) Y) else 0) := by
  obtain ⟨C,hC,hbound⟩ := second_handle_inner_abs_uniform (d.length+1)
  have hs := (hbound (t::d) rfl 0 (by simp) Y hY).1
  simpa [List.eraseIdx,Nat.add_assoc] using hs
end WP.HigherOrder
