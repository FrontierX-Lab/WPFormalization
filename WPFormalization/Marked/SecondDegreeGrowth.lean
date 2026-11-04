import WPFormalization.Marked.SecondDegreeLayer
import WPFormalization.HigherOrder.Coherence
/-! Uniform cubic growth of the original second degree recursion layer.
The bound is pointwise in the kernel index, with the genuine merger and
contraction corrections and both finite separating indicators. -/
noncomputable section
open Set
namespace WP.Analysis
lemma second_weighted_center_bound (a v z L M Q : ℝ) (hL : 1 ≤ L) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (ha : |a| ≤ M) (hv : |a*v| ≤ M) (hz : |z| ≤ Q*L^2) :
    |a*(v-z)| ≤ M*(1+Q)*L^2 := by
  have hL2 : 1 ≤ L^2 := by nlinarith
  rw [mul_sub]
  calc _ ≤ |a*v|+|a*z| := abs_sub _ _
       _ ≤ M+M*(Q*L^2) := add_le_add hv (by rw [abs_mul];exact mul_le_mul ha hz (abs_nonneg _) hM)
       _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hL2 hM]
end WP.Analysis
namespace WP
lemma secondDegreeCountLayer_abs_uniform (p : ℕ) (hp : 1 ≤ p) : ∃ C : ℝ,0<C ∧
    ∀ t : ℕ,∀ d : List ℕ,(t::d).length=p → ∀ l : ℕ,∀ Y∈Icc (0:ℝ) y₀,
      |secondDegreeCountLayer Y t d l| ≤ C*(((t::d).sum:ℝ)+l+1)^3 := by
  obtain ⟨M,hM,hcoeff⟩ := second_prefactor_coefficients_uniform p
  obtain ⟨Qm,hQm,hδm⟩ := degreeCorrection_uniform_quadratic_bound (p-1)
  obtain ⟨Qh,hQh,hδh⟩ := degreeCorrection_uniform_quadratic_bound (p+1)
  obtain ⟨T,hθ⟩ := uniform_kernel_moments.1
  let B : ℝ := max 1 T
  have hB : 0<B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hMp : 0<M := lt_of_lt_of_le zero_lt_one hM
  let Cm : ℝ := M*(1+Qm)
  let Ch : ℝ := M*(1+Qh)
  let Ct : ℝ := M^2*((p:ℝ)^2+B/2+1/2)
  let K : ℝ := (p:ℝ)+2
  have hCm : 0<Cm := by dsimp [Cm];positivity
  have hCh : 0<Ch := by dsimp [Ch];positivity
  have hCt : 0<Ct := by dsimp [Ct];positivity
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨K*Cm+2*Ch+Ct,by positivity,?_⟩
  intro t d hd l Y hY
  let L : ℝ := ((t::d).sum:ℝ)+l+1
  have hL : 1 ≤ L := by dsimp [L];linarith [Nat.cast_nonneg (α:=ℝ) (t::d).sum,Nat.cast_nonneg (α:=ℝ) l]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hL3 : 1 ≤ L^3 := by simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hL 3
  let coeff := fun j : ℕ => 2*(d[j]!:ℝ)+1
  let fm := fun j : ℕ => if 1 ≤ t+d[j]!+l then
    1-transportBeta d.length Y-degreeCorrection (mergerProfile t d l j) Y else 0
  let fh := fun u : ℕ => 1-transportBeta (d.length+2) Y-HigherOrder.alpha (d.length+1) Y-
    degreeCorrection (contractionProfile t d l u) Y
  let v := (if 2 ≤ t+l then (Nat.choose (zeros d) 2:ℝ)+theta Y 1/2 else 0)+
    (if 3 ≤ t+l then (1/2:ℝ) else 0)
  have hdlen : d.length+1=p := by simpa only [List.length_cons] using hd
  have hcoeff0 (j : ℕ) : 0 ≤ coeff j := by dsimp only [coeff];positivity
  have hcm : (∑j ∈ Finset.range d.length,coeff j) ≤ K*L := by
    have hsum : (∑j ∈ Finset.range d.length,coeff j)=2*(d.sum:ℝ)+d.length := by
      dsimp only [coeff]
      rw [Finset.sum_add_distrib,←Finset.mul_sum]
      have he := sum_range_getElem d (fun k : ℕ => (k:ℝ))
      have hc : (d.map (fun k : ℕ => (k:ℝ))).sum=(d.sum:ℝ) := (map_list_sum (Nat.castAddMonoidHom ℝ) d).symm
      rw [hc] at he
      simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    rw [hsum]
    have hdL : (d.sum:ℝ) ≤ L := by dsimp [L];simp only [List.sum_cons,Nat.cast_add];linarith [Nat.cast_nonneg (α:=ℝ) t,Nat.cast_nonneg (α:=ℝ) l]
    have hlen : (d.length:ℝ) ≤ p := by exact_mod_cast (show d.length ≤ p by omega)
    have hpL : (p:ℝ) ≤ (p:ℝ)*L := by nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) p) (sub_nonneg.mpr hL)]
    dsimp [K]
    nlinarith
  have hmerger_term (j : ℕ) (hj : j ∈ Finset.range d.length) : |A Y*fm j| ≤ Cm*L^2 := by
    have hj' := Finset.mem_range.mp hj
    dsimp only [fm]
    split_ifs
    · have hlen : (mergerProfile t d l j).length=p-1 := by
        simp only [mergerProfile,List.length_cons,List.length_eraseIdx_of_lt hj']
        omega
      have hsum : (mergerProfile t d l j).sum ≤ (t::d).sum+l := by
        have hs : d[j]!+(d.eraseIdx j).sum=d.sum := by simpa [hj'] using (List.getElem_cons_eraseIdx_perm hj').sum_eq
        simp only [mergerProfile,List.sum_cons]
        omega
      have hsumR : ((mergerProfile t d l j).sum:ℝ) ≤ ((t::d).sum:ℝ)+l := by exact_mod_cast hsum
      have hδ : |degreeCorrection (mergerProfile t d l j) Y| ≤ Qm*L^2 := by
        apply (hδm _ hlen Y hY).trans
        dsimp only [L]
        gcongr
      have hAv : |A Y*(1-transportBeta d.length Y)| ≤ M := by
        simpa only [show d.length=p-1 by omega] using (hcoeff Y hY).2.1
      exact Analysis.second_weighted_center_bound _ _ _ L M Qm hL hMp.le hQm.le (hcoeff Y hY).1 hAv hδ
    · simp only [mul_zero,abs_zero]
      positivity
  have hmerger : |A Y*(∑j ∈ Finset.range d.length,coeff j*fm j)| ≤ (K*Cm)*L^3 := by
    have heq : A Y*(∑j ∈ Finset.range d.length,coeff j*fm j)=
        ∑j ∈ Finset.range d.length,coeff j*(A Y*fm j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq]
    calc _ ≤ ∑j ∈ Finset.range d.length,|coeff j*(A Y*fm j)| := Finset.abs_sum_le_sum_abs _ _
         _ = ∑j ∈ Finset.range d.length,coeff j*|A Y*fm j| := by
           apply Finset.sum_congr rfl
           intro j hj
           rw [abs_mul,abs_of_nonneg (hcoeff0 j)]
         _ ≤ ∑j ∈ Finset.range d.length,coeff j*(Cm*L^2) :=
           Finset.sum_le_sum (fun j hj=>mul_le_mul_of_nonneg_left (hmerger_term j hj) (hcoeff0 j))
         _ = (∑j ∈ Finset.range d.length,coeff j)*(Cm*L^2) := by rw [Finset.sum_mul]
         _ ≤ (K*L)*(Cm*L^2) := mul_le_mul_of_nonneg_right hcm (by positivity)
         _ = _ := by ring
  have hhandle_term (u : ℕ) (hu : u ∈ Finset.range (t+l-1)) : |A Y*fh u| ≤ Ch*L^2 := by
    have hlen : (contractionProfile t d l u).length=p+1 := by
      simp only [contractionProfile,List.length_cons]
      omega
    have hsum : (contractionProfile t d l u).sum ≤ (t::d).sum+l := by
      have hu' := Finset.mem_range.mp hu
      simp only [contractionProfile,List.sum_cons]
      omega
    have hsumR : ((contractionProfile t d l u).sum:ℝ) ≤ ((t::d).sum:ℝ)+l := by exact_mod_cast hsum
    have hδ : |degreeCorrection (contractionProfile t d l u) Y| ≤ Qh*L^2 := by
      apply (hδh _ hlen Y hY).trans
      dsimp only [L]
      gcongr
    have hAv : |A Y*(1-transportBeta (d.length+2) Y-HigherOrder.alpha (d.length+1) Y)| ≤ M := by
      simpa only [show d.length+2=p+1 by omega,hdlen] using (hcoeff Y hY).2.2
    exact Analysis.second_weighted_center_bound _ _ _ L M Qh hL hMp.le hQh.le (hcoeff Y hY).1 hAv hδ
  have hnL : ((t+l-1:ℕ):ℝ) ≤ L := by
    dsimp only [L]
    exact_mod_cast (show t+l-1 ≤ (t::d).sum+l+1 by simp only [List.sum_cons];omega)
  have hhandle : |2*A Y*(∑u ∈ Finset.range (t+l-1),fh u)| ≤ (2*Ch)*L^3 := by
    have heq : 2*A Y*(∑u ∈ Finset.range (t+l-1),fh u)=
        2*(∑u ∈ Finset.range (t+l-1),A Y*fh u) := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring
    rw [heq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc _ ≤ 2*(∑u ∈ Finset.range (t+l-1),|A Y*fh u|) := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
         _ ≤ 2*(∑u ∈ Finset.range (t+l-1),Ch*L^2) :=
           mul_le_mul_of_nonneg_left (Finset.sum_le_sum hhandle_term) (by norm_num)
         _ = 2*(((t+l-1:ℕ):ℝ)*(Ch*L^2)) := by simp [nsmul_eq_mul]
         _ ≤ 2*(L*(Ch*L^2)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnL (by positivity)) (by norm_num)
         _ = _ := by ring
  have hθ0 := theta_nonneg Y hY 1
  have hθB : theta Y 1 ≤ B := ((hθ Y hY).2.2 1).1.trans (le_max_right _ _)
  have hz : zeros d ≤ p := by have := HigherOrder.zeros_add_positiveCount d;omega
  have hchoose0 : 0 ≤ (Nat.choose (zeros d) 2:ℝ) := Nat.cast_nonneg _
  have hchoose : (Nat.choose (zeros d) 2:ℝ) ≤ (p:ℝ)^2 := by
    have hc : (Nat.choose (zeros d) 2:ℝ) ≤ (zeros d:ℝ)^2 := by exact_mod_cast Nat.choose_le_pow (zeros d) 2
    exact hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hz) 2)
  have hv0 : 0 ≤ v := by dsimp [v];split_ifs <;> positivity
  have hv : v ≤ (p:ℝ)^2+B/2+1/2 := by
    dsimp only [v]
    split_ifs <;> linarith
  have hA2 : (A Y)^2 ≤ M^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcoeff Y hY).1 2
  have htail : |(A Y)^2*v| ≤ Ct*L^3 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_nonneg hv0]
    have hi : (A Y)^2*v ≤ Ct := mul_le_mul hA2 hv hv0 (sq_nonneg M)
    exact hi.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hL3 hCt.le)
  change |A Y*(∑j ∈ Finset.range d.length,coeff j*fm j)+2*A Y*(∑u ∈ Finset.range (t+l-1),fh u)+(A Y)^2*v| ≤ (K*Cm+2*Ch+Ct)*L^3
  calc _ ≤ (|A Y*(∑j ∈ Finset.range d.length,coeff j*fm j)|+|2*A Y*(∑u ∈ Finset.range (t+l-1),fh u)|)+|(A Y)^2*v| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
       _ ≤ ((K*Cm)*L^3+(2*Ch)*L^3)+Ct*L^3 := add_le_add (add_le_add hmerger hhandle) htail
       _ = _ := by ring
end WP
