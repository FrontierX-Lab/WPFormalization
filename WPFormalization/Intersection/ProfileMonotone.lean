import WPFormalization.Intersection.PainleveComparison
import Mathlib
/-! Actual degree monotonicity on the closed parameter interval. The proof
uses the exact finite positive convolution and the already registered kernel
bounds. The adjacent-difference identity is purely finite algebra and does
not require those kernel positivity inputs. No new assumption is introduced. -/
noncomputable section
open Set
namespace WP

lemma normalized_perm (P : PsiTheory) (g : ℕ) {d e : List ℕ} (hp : d.Perm e) (Y : ℝ) :
    normalized P g d Y = normalized P g e Y := by
  have hlen := hp.length_eq
  have hsum := hp.sum_eq
  have hdef : deficit g d = deficit g e := by simp only [deficit, hlen, hsum]
  have hprod := (hp.map (fun k => (oddFactorial k : ℝ))).prod_eq
  have hpsi (l : List ℕ) : pure P g (d++l) = pure P g (e++l) := by
    exact P.symmetry g _ _ ((hp.append_right l).map Int.ofNat)
  unfold normalized shifted
  rw [hdef]
  simp only [hlen, hsum, hprod, hpsi]

lemma normalized_nonneg_nonempty (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hn : 1 ≤ d.length) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    0 ≤ normalized P g d Y :=
  (normalized_critical_nonneg P g d).trans (normalized_pi_le P g d hn Y hY)

lemma normalizedChildren_nonneg_step (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    (hh : 2 ≤ complexity g (d.length+1)) (hd : ∀ k ∈ d, 0 ≤ k)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    0 ≤ normalizedChildren P g p d Y := by
  apply (normalizedChildren_critical_nonneg P g p d hd).trans
  apply normalizedChildren_pi_le_step P g p (complexity g (d.length+1)) d Y hh rfl hd
  intro g' c hn hc
  unfold piSigned
  split_ifs
  · exact normalized_pi_le P g' (c.map Int.toNat) (by simpa using hn) Y hY
  · exact le_rfl

lemma normalized_cons_raise_le (P : PsiTheory) (g p : ℕ) (d : List ℕ)
    (hs : Stable g (d.length+1)) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    normalized P g ((p+1)::d) Y ≤ normalized P g (p::d) Y := by
  by_cases hd : ((p+1)::d).sum ≤ dimension g (d.length+1)
  · have hd0 : (p::d).sum ≤ dimension g (d.length+1) := by
      simp only [List.sum_cons] at hd ⊢
      omega
    by_cases hh : 2 ≤ complexity g (d.length+1)
    · have hm : 1 ≤ deficit g (p::d) := by unfold deficit; simp only [List.length_cons,List.sum_cons] at *;omega
      have he : deficit g ((p+1)::d)+1 = deficit g (p::d) := by
        unfold deficit
        simp only [List.length_cons,List.sum_cons] at *
        omega
      rw [normalized_positive_convolution P g (p+1) d Y hh hd hY,
        normalized_positive_convolution P g p d Y hh hd0 hY, he,
        Finset.sum_range_succ']
      have hbase : 0 ≤ theta Y 0 * normalizedChildren P g p (d.map Int.ofNat) Y := by
        apply mul_nonneg (by have := piTheta_ge_one Y hY 0;linarith)
        exact normalizedChildren_nonneg_step P g p _ (by simpa using hh)
          (by intro k hk;obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hk;exact Int.natCast_nonneg j) Y hY
      simp only [Nat.add_zero]
      have hsums :
          (∑ l ∈ Finset.range (deficit g (p::d)-1+1), theta Y l *
            normalizedChildren P g (p+1+l) (d.map Int.ofNat) Y) ≤
          (∑ l ∈ Finset.range (deficit g (p::d)-1+1), theta Y (l+1) *
            normalizedChildren P g (p+(l+1)) (d.map Int.ofNat) Y) := by
        apply Finset.sum_le_sum
        intro l hl
        rw [show p+1+l=p+(l+1) by omega]
        apply mul_le_mul_of_nonneg_right
        · obtain ⟨C,hC⟩ := uniform_kernel_moments.1
          exact (hC Y hY).2.1 (by omega)
        · exact normalizedChildren_nonneg_step P g (p+(l+1)) _ (by simpa using hh)
            (by intro k hk;obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hk;exact Int.natCast_nonneg j) Y hY
      have hlen : deficit g (p::d)-1+1=deficit g (p::d) := by omega
      rw [hlen] at hsums
      exact hsums.trans (le_add_of_nonneg_right hbase)
    · have hg : g = 1 := by unfold Stable at hs;unfold complexity at hh;unfold dimension at hd;simp only[List.sum_cons] at hd;omega
      have hdlen : d.length = 0 := by subst g;unfold Stable at hs;unfold complexity at hh;omega
      have hdnil : d = [] := List.length_eq_zero_iff.mp hdlen
      subst g
      subst d
      have hp : p = 0 := by norm_num [dimension] at hd;omega
      subst p
      rw [(initial_amplitudes P Y hY).2.1, (initial_amplitudes P Y hY).2.2]
      have ht := piTheta_ge_one Y hY 1
      linarith
  · have hex : dimension g ((p+1)::d).length < ((p+1)::d).sum := by simpa using Nat.lt_of_not_ge hd
    rw [normalized_excess P g ((p+1)::d) Y hex]
    exact normalized_nonneg_nonempty P g (p::d) (by simp) Y hY

lemma normalized_set_raise_le (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (i : ℕ) (hi : i < d.length)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    normalized P g (d.set i (d[i]!+1)) Y ≤ normalized P g d Y := by
  have hp0 : (d[i]!::d.eraseIdx i).Perm d := by
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
      using List.getElem_cons_eraseIdx_perm hi
  have hp1 := List.set_perm_cons_eraseIdx hi (d[i]!+1)
  rw [normalized_perm P g hp1 Y, ← normalized_perm P g hp0 Y]
  apply normalized_cons_raise_le P g (d[i]!) (d.eraseIdx i) _ Y hY
  have hlen : (d.eraseIdx i).length+1=d.length := by simpa using hp0.length_eq
  rwa [hlen]

lemma normalized_le_all_zero_aux (P : PsiTheory) (g : ℕ) (Y : ℝ)
    (hY : Y ∈ Icc 0 y₀) (n : ℕ) :
    ∀ d : List ℕ, d.sum = n → Stable g d.length →
      normalized P g d Y ≤ normalized P g (List.replicate d.length 0) Y := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro d hd hs
    by_cases hz : d.sum = 0
    · have he : d = List.replicate d.length 0 :=
        List.eq_replicate_of_mem (List.sum_eq_zero_iff_forall_eq_nat.mp hz)
      rw [he]
      simp only [List.length_replicate]
      exact le_rfl
    · have hpos : ∃ a ∈ d, 0 < a :=
        List.sum_pos_iff_exists_pos_nat.mp (Nat.pos_of_ne_zero hz)
      obtain ⟨a,ha,hapos⟩ := hpos
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hapos)
      obtain ⟨l,r,rfl⟩ := List.mem_iff_append.mp ha
      let e := l ++ k::r
      have helen : e.length = (l ++ (k+1)::r).length := by simp [e]
      have hes : e.sum < n := by simp only [e,List.sum_append,List.sum_cons] at hd ⊢;omega
      have hei : l.length < e.length := by simp [e]
      have hset : e.set l.length (e[l.length]!+1) = l ++ (k+1)::r := by simp [e]
      have hstep := normalized_set_raise_le P g e (by simpa only [helen] using hs)
        l.length hei Y hY
      rw [hset] at hstep
      exact hstep.trans (by simpa only [helen] using ih e.sum hes e rfl (by rwa [helen]))

lemma normalized_le_all_zero (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    normalized P g d Y ≤ normalized P g (List.replicate d.length 0) Y :=
  normalized_le_all_zero_aux P g Y hY d.sum d rfl hs

lemma normalized_profile_bounds (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hn : 1 ≤ d.length) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    0 ≤ normalized P g d Y / normalized P g (List.replicate d.length 0) Y ∧
    normalized P g d Y / normalized P g (List.replicate d.length 0) Y ≤ 1 := by
  have hd := normalized_nonneg_nonempty P g d hn Y hY
  have hz := normalized_nonneg_nonempty P g (List.replicate d.length 0)
    (by simpa only [List.length_replicate] using hn) Y hY
  refine ⟨div_nonneg hd hz, ?_⟩
  by_cases he : normalized P g (List.replicate d.length 0) Y = 0
  · simp [he]
  · exact (div_le_one (lt_of_le_of_ne hz (Ne.symm he))).2 (normalized_le_all_zero P g d hs Y hY)

lemma profile_monotone_proof (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (i : ℕ) (hi : i < d.length)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    normalized P g (d.set i (d[i]!+1)) Y ≤ normalized P g d Y ∧
    0 ≤ normalized P g d Y / normalized P g (List.replicate d.length 0) Y ∧
    normalized P g d Y / normalized P g (List.replicate d.length 0) Y ≤ 1 := by
  exact ⟨normalized_set_raise_le P g d hs i hi Y hY,
    normalized_profile_bounds P g d hs (by omega) Y hY⟩
end WP

namespace WP
lemma finite_adjacent_convolution_difference (N : ℕ) (t V : ℕ → ℝ) :
    (∑ j ∈ Finset.range (N+1), t j * V j) -
      (∑ j ∈ Finset.range N, t j * V (j+1)) =
      ∑ j ∈ Finset.range (N+1),
        (t j - if j=0 then 0 else t (j-1))*V j := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
    Nat.add_sub_cancel, ite_true, sub_zero]
  simp_rw [sub_mul,Finset.sum_sub_distrib]
  ring

lemma normalized_adjacent_degree_difference (P : PsiTheory) (g p : ℕ) (d : List ℕ)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) (hh : 2 ≤ complexity g (d.length+1))
    (hd : (p::d).sum ≤ dimension g (d.length+1)) :
    normalized P g (p::d) Y - normalized P g ((p+1)::d) Y =
      ∑ l ∈ Finset.range (deficit g (p::d)+1), weight Y l *
        normalizedChildren P g (p+l) (d.map Int.ofNat) Y := by
  have hu1 : normalized P g ((p+1)::d) Y =
      ∑ l ∈ Finset.range (deficit g (p::d)), theta Y l *
        normalizedChildren P g (p+(l+1)) (d.map Int.ofNat) Y := by
    by_cases hd1 : ((p+1)::d).sum ≤ dimension g (d.length+1)
    · rw [normalized_positive_convolution P g (p+1) d Y hh hd1 hY]
      have hm : deficit g ((p+1)::d)+1 = deficit g (p::d) := by
        unfold deficit
        simp only [List.length_cons,List.sum_cons] at *
        omega
      rw [hm]
      apply Finset.sum_congr rfl
      intro l hl
      rw [show p+1+l=p+(l+1) by omega]
    · have he : dimension g ((p+1)::d).length < ((p+1)::d).sum := by
        simpa using Nat.lt_of_not_ge hd1
      have hm : deficit g (p::d)=0 := by
        unfold deficit
        simp only [List.length_cons,List.sum_cons] at *
        omega
      rw [normalized_excess P g ((p+1)::d) Y he,hm]
      simp
  rw [normalized_positive_convolution P g p d Y hh hd hY,hu1]
  simpa only [weight] using finite_adjacent_convolution_difference
    (deficit g (p::d)) (theta Y)
    (fun l => normalizedChildren P g (p+l) (d.map Int.ofNat) Y)
end WP
