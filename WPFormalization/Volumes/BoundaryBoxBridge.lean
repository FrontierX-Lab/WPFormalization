import WPFormalization.Volumes.BoundaryCoefficientBridge
import WPFormalization.Marked.ExternalStringFinite

noncomputable section
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology

lemma mixedBracket_excess_zero (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hd : dimension g d.length < d.sum) : mixedBracket P g d = 0 := by
  simp [mixedBracket,shifted,not_le.mpr hd]

lemma boundaryVolumeModel_eq_box (P : PsiTheory) (g p B : ℕ)
    (hB : dimension g p ≤ B) (L : Fin p → ℝ) :
    boundaryVolumeModel P g p L =
      ∑ b ∈ externalDegreeBox p B,
        mixedBracket P g (List.ofFn b)*boundaryDegreeWeight p L b := by
  classical
  unfold boundaryVolumeModel
  apply Finset.sum_subset
  · intro b hb
    apply (mem_externalDegreeBox p B b).mpr
    intro i
    have hs := (mem_degreeTuples_iff g p b).mp hb
    exact (Finset.single_le_sum (fun i _ => Nat.zero_le (b i)) (Finset.mem_univ i)).trans (hs.trans hB)
  · intro b hb hnot
    have hd := lt_of_not_ge (mt (mem_degreeTuples_iff g p b).mpr hnot)
    have he : mixedBracket P g (List.ofFn b)=0 :=
      mixedBracket_excess_zero P g _ (by simpa only [List.sum_ofFn,List.length_ofFn] using hd)
    rw [he,zero_mul]

lemma externalDegreeBox_sum_append (q p B : ℕ) (F : (Fin (q+p) → ℕ) → ℝ) :
    (∑ d ∈ externalDegreeBox (q+p) B, F d) =
      ∑ a ∈ externalDegreeBox q B, ∑ b ∈ externalDegreeBox p B, F (Fin.append a b) := by
  classical
  rw [←Finset.sum_product']
  symm
  apply Finset.sum_bij (fun ab _ => Fin.append ab.1 ab.2)
  · intro ab hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply (mem_externalDegreeBox (q+p) B _).mpr
    apply (Fin.forall_fin_add (m := q) (n := p) (fun i => Fin.append ab.1 ab.2 i ≤ B)).mpr
    constructor
    · intro i
      simpa using (mem_externalDegreeBox q B ab.1).mp ha i
    · intro i
      simpa using (mem_externalDegreeBox p B ab.2).mp hb i
  · intro ab hab cd hcd he
    apply Prod.ext
    · funext i
      have hh := congrFun he (Fin.castAdd p i)
      simpa using hh
    · funext i
      have hh := congrFun he (Fin.natAdd q i)
      simpa using hh
  · intro d hd
    refine ⟨(fun i => d (Fin.castAdd p i),fun i => d (Fin.natAdd q i)),?_,?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact (mem_externalDegreeBox q B _).mpr (fun i => (mem_externalDegreeBox (q+p) B d).mp hd _)
      · exact (mem_externalDegreeBox p B _).mpr (fun i => (mem_externalDegreeBox (q+p) B d).mp hd _)
    · exact Fin.append_castAdd_natAdd
  · intro ab hab
    rfl

lemma boundaryDegreeWeight_append (q p : ℕ) (L : Fin q → ℝ) (M : Fin p → ℝ)
    (a : Fin q → ℕ) (b : Fin p → ℕ) :
    boundaryDegreeWeight (q+p) (Fin.append L M) (Fin.append a b) =
      boundaryDegreeWeight q L a * boundaryDegreeWeight p M b := by
  unfold boundaryDegreeWeight
  rw [Fin.prod_univ_add]
  simp

lemma boundaryDegreeWeight_zero_prefix (q : ℕ) (a : Fin q → ℕ) :
    boundaryDegreeWeight q (fun _ => 0) a = if a=0 then 1 else 0 := by
  classical
  by_cases ha : a=0
  · subst a
    simp [boundaryDegreeWeight]
  · rw [if_neg ha]
    obtain ⟨i,hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact ha (funext hh)
    unfold boundaryDegreeWeight
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma boundaryVolumeModel_zero_prefix_box (P : PsiTheory) (g q p B : ℕ)
    (hB : dimension g (q+p) ≤ B) (L : Fin p → ℝ) :
    boundaryVolumeModel P g (q+p) (Fin.append (fun _ : Fin q => 0) L) =
      ∑ b ∈ externalDegreeBox p B,
        mixedBracket P g (List.replicate q 0 ++ List.ofFn b) * boundaryDegreeWeight p L b := by
  classical
  rw [boundaryVolumeModel_eq_box P g (q+p) B hB,
    externalDegreeBox_sum_append]
  have he (a : Fin q → ℕ) (b : Fin p → ℕ) :
      mixedBracket P g (List.ofFn (Fin.append a b)) *
        boundaryDegreeWeight (q+p) (Fin.append (fun _ => 0) L) (Fin.append a b) =
      if a=0 then mixedBracket P g (List.replicate q 0 ++ List.ofFn b)*boundaryDegreeWeight p L b else 0 := by
    rw [boundaryDegreeWeight_append,boundaryDegreeWeight_zero_prefix]
    split_ifs with ha
    · subst a
      have hz : List.ofFn (0 : Fin q → ℕ) = List.replicate q 0 := by
        change List.ofFn (fun _ : Fin q => 0) = _
        simp
      simp only [List.ofFn_fin_append,hz,one_mul]
    · simp
  simp only [he]
  have hh (a : Fin q → ℕ) :
      (∑ b ∈ externalDegreeBox p B, if a=0 then
        mixedBracket P g (List.replicate q 0 ++ List.ofFn b)*boundaryDegreeWeight p L b else 0) =
      if a=0 then ∑ b ∈ externalDegreeBox p B,
        mixedBracket P g (List.replicate q 0 ++ List.ofFn b)*boundaryDegreeWeight p L b else 0 := by
    split_ifs <;> simp_all
  simp only [hh]
  have hzero : (0 : Fin q → ℕ) ∈ externalDegreeBox q B := by simp
  simp [hzero]

end WP.BoundaryConvolution
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology

lemma boundary_polynomial_term_normalization_all (P : PsiTheory) (g p : ℕ)
    (L : Fin p → ℝ) (b : Fin p → ℕ) :
    mixedBracket P g (List.ofFn b)*boundaryDegreeWeight p L b /
      (2*Real.pi^2)^(dimension g p) =
      shifted P g (List.ofFn b) 0 /
        (∏ i, (oddFactorial (b i):ℝ)) *
          ∏ i, ((L i)^2/(4*Real.pi^2))^(b i)/(b i).factorial := by
  by_cases hb : b ∈ degreeTuples g p
  · exact boundary_polynomial_term_normalization P g p L b hb
  · have hd : dimension g p < ∑ i,b i := lt_of_not_ge (mt (mem_degreeTuples_iff g p b).mpr hb)
    have hz : shifted P g (List.ofFn b) 0=0 := by
      simp only [shifted,List.length_ofFn,List.sum_ofFn]
      simp [not_le.mpr hd]
    simp [mixedBracket,hz]

lemma boundary_polynomial_zero_prefix_term (P : PsiTheory) (g q p : ℕ)
    (L : Fin p → ℝ) (b : Fin p → ℕ) :
    mixedBracket P g (List.replicate q 0 ++ List.ofFn b)*boundaryDegreeWeight p L b /
      (2*Real.pi^2)^(dimension g (q+p)) =
      shifted P g (List.replicate q 0 ++ List.ofFn b) 0 /
        (∏ i, (oddFactorial (b i):ℝ)) *
          ∏ i, ((L i)^2/(4*Real.pi^2))^(b i)/(b i).factorial := by
  have hh := boundary_polynomial_term_normalization_all P g (q+p)
    (Fin.append (fun _ : Fin q => 0) L) (Fin.append (fun _ : Fin q => 0) b)
  have hz : boundaryDegreeWeight q (fun _ => 0) (fun _ => 0)=1 := by
    simp [boundaryDegreeWeight]
  rw [boundaryDegreeWeight_append,hz,one_mul] at hh
  have hodd : oddFactorial 0=1 := by norm_num [oddFactorial]
  simpa [List.ofFn_fin_append,Fin.prod_univ_add,hodd] using hh

lemma boundaryVolumeModel_zero_prefix_scaled_box (P : PsiTheory) (g q p B : ℕ)
    (hB : dimension g (q+p) ≤ B) (L : Fin p → ℝ) :
    boundaryVolumeModel P g (q+p) (Fin.append (fun _ : Fin q => 0) L) /
      (2*Real.pi^2)^(dimension g (q+p)) =
      ∑ b ∈ externalDegreeBox p B,
        shifted P g (List.replicate q 0 ++ List.ofFn b) 0 /
          (∏ i, (oddFactorial (b i):ℝ)) *
            ∏ i, ((L i)^2/(4*Real.pi^2))^(b i)/(b i).factorial := by
  rw [boundaryVolumeModel_zero_prefix_box P g q p B hB L,Finset.sum_div]
  exact Finset.sum_congr rfl (fun b hb => boundary_polynomial_zero_prefix_term P g q p L b)

end WP.BoundaryConvolution
