import WPFormalization.HigherOrder.FirstScalarCoefficients
import WPFormalization.HigherOrder.SecondKernelSum

/-! Exact second-order merger and nonseparating coefficients of the defined triangular hierarchy; all infinite sums are justified. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

lemma coefficientSum_constant (f : ℕ→Series) :
    constantCoeff (coefficientSum f)=∑'l:ℕ,constantCoeff (f l) := by
  rw [←coeff_zero_eq_constantCoeff,coefficientSum_coeff]

lemma coeff_two_C_shift_mul (a c : ℝ) (f : Series) :
    PowerSeries.coeff 2 (C a*shiftVariable c*f)=a*(c*constantCoeff f+PowerSeries.coeff 1 f) := by
  rw [coeff_two_mul,coeff_two_mul,PowerSeries.coeff_one_mul]
  simp [shiftVariable_constant,shiftVariable_one,shiftVariable_two]
  <;>ring

lemma hierarchy_one_profile_constant (P : PsiTheory) (Y : ℝ) (d : List ℕ) :
    constantCoeff ((hierarchyJet P Y 1).profile d)=1 := (hierarchy_unit_constants P Y 1).1 d
lemma hierarchy_one_cusp_constant (P : PsiTheory) (Y : ℝ) (p : ℕ) :
    constantCoeff ((hierarchyJet P Y 1).cusp p)=1 := (hierarchy_unit_constants P Y 1).2.1 p
lemma hierarchy_one_genus_constant (P : PsiTheory) (Y : ℝ) (p : ℕ) :
    constantCoeff ((hierarchyJet P Y 1).genus p)=1 := (hierarchy_unit_constants P Y 1).2.2 p
lemma hierarchy_one_profile_one (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (d : List ℕ) :
    PowerSeries.coeff 1 ((hierarchyJet P Y 1).profile d)= -degreeCorrection d Y := by
  rw [hierarchy_profile_stable P Y d 1 1 le_rfl,profileCoefficient_one P Y hY]
lemma hierarchy_one_cusp_one (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (p : ℕ) :
    PowerSeries.coeff 1 ((hierarchyJet P Y 1).cusp p)= -transportBeta p Y := by
  rw [hierarchy_cusp_stable P Y p 1 1 le_rfl,cuspCoefficient_one P p Y hY]
lemma hierarchy_one_genus_one (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (p : ℕ) :
    PowerSeries.coeff 1 ((hierarchyJet P Y 1).genus p)= -alpha p Y := by
  rw [hierarchy_genus_stable P Y p 1 1 le_rfl,genusCoefficient_one P p Y hY]

lemma mergerSeries_two_raw (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (t : ℕ) (d : List ℕ) :
    PowerSeries.coeff 2 (mergerSeries Y (hierarchyJet P Y 1) t d)=
      A Y*((1-transportBeta d.length Y)*
        (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
          ∑'l:ℕ,if 1≤t+d[j]!+l then weight Y l else 0)+
        (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
          ∑'l:ℕ,if 1≤t+d[j]!+l then weight Y l* -degreeCorrection ((t+d[j]!+l-1)::d.eraseIdx j) Y else 0)) := by
  unfold mergerSeries
  rw [mul_assoc,coeff_two_C_shift_mul]
  simp only [PowerSeries.coeff_one_mul,map_mul,map_sum,complexityShift_constant,
    hierarchy_one_cusp_constant,hierarchy_one_profile_constant,complexityShift_one,
    hierarchy_one_cusp_one P Y hY,hierarchy_one_profile_one P Y hY,
    PowerSeries.constantCoeff_C,PowerSeries.coeff_C_mul,coefficientSum_coeff,coefficientSum_constant]
  have hz (j l : ℕ) : constantCoeff (if 1≤t+d[j]!+l then
      C (weight Y l)*complexityShift 1 ((hierarchyJet P Y 1).profile ((t+d[j]!+l-1)::d.eraseIdx j)) else 0)=
      if 1≤t+d[j]!+l then weight Y l else 0 := by
    split_ifs <;>simp [hierarchy_one_profile_constant]
  have ho (j l : ℕ) : PowerSeries.coeff 1 (if 1≤t+d[j]!+l then
      C (weight Y l)*complexityShift 1 ((hierarchyJet P Y 1).profile ((t+d[j]!+l-1)::d.eraseIdx j)) else 0)=
      if 1≤t+d[j]!+l then weight Y l* -degreeCorrection ((t+d[j]!+l-1)::d.eraseIdx j) Y else 0 := by
    split_ifs <;>simp [complexityShift_one,hierarchy_one_profile_one P Y hY]
  simp_rw [hz,ho]
  ring
lemma merger_front_coefficient_combine (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀)
    (t : ℕ) (d : List ℕ) (j : ℕ) (hj : j<d.length) :
    (1-transportBeta d.length Y)*(∑'l:ℕ,if 1≤t+d[j]!+l then weight Y l else 0)+
      (∑'l:ℕ,if 1≤t+d[j]!+l then weight Y l* -degreeCorrection ((t+d[j]!+l-1)::d.eraseIdx j) Y else 0)=
      (∑'l:ℕ,if 1≤t+d[j]!+l then weight Y l*(1-transportBeta d.length Y-
        degreeCorrection ((t+d[j]!+l-1)::d.eraseIdx j) Y) else 0) := by
  let f : ℕ→ℝ:=fun l=>if 1≤t+d[j]!+l then weight Y l else 0
  let v : ℕ→ℝ:=fun l=>if 1≤t+d[j]!+l then weight Y l* -degreeCorrection ((t+d[j]!+l-1)::d.eraseIdx j) Y else 0
  let c:=1-transportBeta d.length Y
  have hf : Summable f := (weight_cutoff_hasSum Y hY 1 (t+d[j]!)).summable
  have hfront:=second_merger_front_summable Y hY t d j hj
  have hv : Summable v := by
    convert! hfront.sub (hf.mul_left c) using 1
    funext l
    dsimp [v,c,f]
    split_ifs <;>ring
  have he : (fun l:ℕ=>c*f l+v l)=(fun l:ℕ=>if 1≤t+d[j]!+l then
      weight Y l*(1-transportBeta d.length Y-degreeCorrection ((t+d[j]!+l-1)::d.eraseIdx j) Y) else 0) := by
    funext l
    dsimp [c,f,v]
    split_ifs <;>ring
  have hh:=((hf.hasSum.mul_left c).add hv.hasSum).tsum_eq
  rw [he] at hh
  simpa only [tsum_mul_left] using hh.symm

lemma mergerSeries_two (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (t : ℕ) (d : List ℕ) :
    PowerSeries.coeff 2 (mergerSeries Y (hierarchyJet P Y 1) t d)=
      A Y*(∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
        ∑'l:ℕ,if 1≤t+d[j]!+l then weight Y l*(1-transportBeta d.length Y-
          degreeCorrection ((t+d[j]!+l-1)::d.eraseIdx j) Y) else 0) := by
  rw [mergerSeries_two_raw P Y hY t d]
  congr 1
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [←merger_front_coefficient_combine Y hY t d j (Finset.mem_range.mp hj)]
  ring
lemma nonseparatingSeries_two_raw (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (t : ℕ) (d : List ℕ) :
    PowerSeries.coeff 2 (nonseparatingSeries Y (hierarchyJet P Y 1) t d)=
      2*A Y*((1-transportBeta (d.length+2) Y-alpha (d.length+1) Y)*
        (∑'l:ℕ,weight Y l*(t+l-1:ℕ))+
        (∑'l:ℕ,weight Y l*(∑u∈Finset.range (t+l-1),
          -degreeCorrection (u::(t+l-2-u)::d) Y))) := by
  rw [nonseparatingSeries,mul_assoc (C (2*A Y)*shiftVariable 1),
    mul_assoc (C (2*A Y)*shiftVariable 1),coeff_two_C_shift_mul]
  simp only [PowerSeries.coeff_one_mul,map_mul,map_sum,complexityShift_constant,
    hierarchy_one_cusp_constant,hierarchy_one_genus_constant,hierarchy_one_profile_constant,
    complexityShift_one,hierarchy_one_cusp_one P Y hY,hierarchy_one_genus_one P Y hY,
    hierarchy_one_profile_one P Y hY,PowerSeries.constantCoeff_C,PowerSeries.coeff_C_mul,
    coefficientSum_coeff,coefficientSum_constant,one_mul,mul_one,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring
lemma weighted_pair_count_summable (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (t : ℕ) :
    Summable (fun l:ℕ=>weight Y l*(t+l-1:ℕ)) := by
  obtain ⟨M,hM,hbound⟩:=canonical_weighted_polynomial_bound 1
  exact (hbound Y hY t 1 (by norm_num) (fun l:ℕ=>(t+l-1:ℕ)) (by
    intro l
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    simp only [one_mul,pow_one]
    exact_mod_cast (show t+l-1≤t+l+1 by omega))).1

lemma handle_front_coefficient_combine (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (t : ℕ) (d : List ℕ) :
    (1-transportBeta (d.length+2) Y-alpha (d.length+1) Y)*
      (∑'l:ℕ,weight Y l*(t+l-1:ℕ))+
      (∑'l:ℕ,weight Y l*(∑u∈Finset.range (t+l-1),-degreeCorrection (u::(t+l-2-u)::d) Y))=
      (∑'l:ℕ,weight Y l*(∑u∈Finset.range (t+l-1),
        (1-transportBeta (d.length+2) Y-alpha (d.length+1) Y-degreeCorrection (u::(t+l-2-u)::d) Y))) := by
  let f : ℕ→ℝ:=fun l=>weight Y l*(t+l-1:ℕ)
  let v : ℕ→ℝ:=fun l=>weight Y l*(∑u∈Finset.range (t+l-1),-degreeCorrection (u::(t+l-2-u)::d) Y)
  let c:=1-transportBeta (d.length+2) Y-alpha (d.length+1) Y
  let F : ℕ→ℝ:=fun l=>weight Y l*(∑u∈Finset.range (t+l-1),
    (1-transportBeta (d.length+2) Y-alpha (d.length+1) Y-degreeCorrection (u::(t+l-2-u)::d) Y))
  have hf : Summable f:=weighted_pair_count_summable Y hY t
  have hF : Summable F := by
    convert! second_handle_front_summable Y hY t d using 1
    funext l
    dsimp [F]
    by_cases hn : 2≤t+l
    · rw [if_pos hn]
    · rw [if_neg hn,show t+l-1=0 by omega]
      simp
  have he : (fun l:ℕ=>c*f l+v l)=F := by
    funext l
    dsimp [c,f,v,F]
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Finset.sum_neg_distrib]
    ring
  have hv : Summable v := by
    convert! hF.sub (hf.mul_left c) using 1
    funext l
    have hh:=congrFun he l
    linarith
  have hh:=((hf.hasSum.mul_left c).add hv.hasSum).tsum_eq
  rw [he] at hh
  exact hh.symm

lemma nonseparatingSeries_two (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (t : ℕ) (d : List ℕ) :
    PowerSeries.coeff 2 (nonseparatingSeries Y (hierarchyJet P Y 1) t d)=
      2*A Y*(∑'l:ℕ,if 2≤t+l then weight Y l*(∑u∈Finset.range (t+l-1),
        (1-transportBeta (d.length+2) Y-alpha (d.length+1) Y-degreeCorrection (u::(t+l-2-u)::d) Y)) else 0) := by
  rw [nonseparatingSeries_two_raw P Y hY t d,handle_front_coefficient_combine Y hY t d]
  congr 1
  apply tsum_congr
  intro l
  by_cases hn : 2≤t+l
  · rw [if_pos hn]
  · rw [if_neg hn,show t+l-1=0 by omega]
    simp

end WP.HigherOrder
