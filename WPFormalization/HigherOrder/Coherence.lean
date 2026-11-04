import WPFormalization.Analysis.UniformKernelMoments
import WPFormalization.HigherOrder.FirstOrder

/-! Coherence of the actual first order of the triangular construction.
The PF6 increment is proved to be the discrete differential of the explicit
quadratic profile correction. Kernel sums then identify the coefficient of
FE3 at the base jet with that increment; telescoping gives the canonical
profile coefficient, discrete curl, symmetry, and arbitrary-path independence.

The pure finite algebra results use no unproved theorem. Identification of the
actual kernel sums uses `uniform_kernel_moments` at q=0,1; that upstream paper
lemma now has a conditional proof from the explicitly registered classical
inputs. No path-independence field is assumed.
-/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

/-- Raise precisely one labeled degree. -/
def raiseDegree (d : List ℕ) (i : ℕ) : List ℕ := d.set i (d[i]!+1)
/-- Number of positive degrees, as in PF5. -/
def positiveCount (d : List ℕ) : ℕ := (d.filter (fun k => 0 < k)).length

/-- The actual leading adjacent increment of PF6, written using the positive count. -/
def leadingIncrement (Y : ℝ) (i : ℕ) (d : List ℕ) : ℝ :=
  A Y * (Theta Y*(2*(d.sum : ℝ)+d.length-3)+2*moment₁ Y+
    if d[i]! = 0 then (positiveCount d : ℝ)+3-d.length else 0)

lemma raiseDegree_length (d : List ℕ) (i : ℕ) :
    (raiseDegree d i).length = d.length := by simp [raiseDegree]

lemma raiseDegree_sum (d : List ℕ) (i : ℕ) (hi : i < d.length) :
    (raiseDegree d i).sum = d.sum+1 := by
  induction d generalizing i with
  | nil => simp at hi
  | cons a d ih =>
    cases i with
    | zero => simp [raiseDegree]; omega
    | succ i =>
      have hi' : i < d.length := by simpa using hi
      simpa [raiseDegree, Nat.add_assoc] using congrArg (fun n => a+n) (ih i hi')

lemma raiseDegree_positiveCount (d : List ℕ) (i : ℕ) (hi : i < d.length) :
    positiveCount (raiseDegree d i) = positiveCount d + if d[i]! = 0 then 1 else 0 := by
  induction d generalizing i with
  | nil => simp at hi
  | cons a d ih =>
    cases i with
    | zero =>
      by_cases ha : a = 0
      · simp [raiseDegree,positiveCount,ha]
      · have ha' : 0 < a := Nat.pos_of_ne_zero ha
        simp [raiseDegree,positiveCount,ha,ha']
    | succ i =>
      have hi' : i < d.length := by simpa using hi
      have h := ih i hi'
      by_cases ha : 0 < a
      · simpa [raiseDegree,positiveCount,ha,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using congrArg Nat.succ h
      · simpa [raiseDegree,positiveCount,ha] using h

lemma leadingIncrement_eq_difference (Y : ℝ) (d : List ℕ) (i : ℕ)
    (hi : i < d.length) :
    leadingIncrement Y i d = degreeCorrection (raiseDegree d i) Y-degreeCorrection d Y := by
  have hs := raiseDegree_sum d i hi
  have hq := raiseDegree_positiveCount d i hi
  unfold leadingIncrement
  change _ =
    A Y*(Theta Y*((((raiseDegree d i).sum : ℝ))^2+((raiseDegree d i).length-4)*
      (raiseDegree d i).sum)+2*moment₁ Y*(raiseDegree d i).sum+
      (positiveCount (raiseDegree d i) : ℝ)*(positiveCount (raiseDegree d i)+5-2*(raiseDegree d i).length)/2) -
    A Y*(Theta Y*((d.sum : ℝ)^2+(d.length-4)*d.sum)+2*moment₁ Y*d.sum+
      (positiveCount d : ℝ)*(positiveCount d+5-2*d.length)/2)
  rw [hs,raiseDegree_length,hq]
  by_cases h : d[i]! = 0
  · simp only [h, if_pos, Nat.cast_add, Nat.cast_one]
    ring
  · simp only [h, if_false, Nat.add_zero, Nat.cast_add, Nat.cast_one]
    ring

lemma raiseDegree_comm (d : List ℕ) (i j : ℕ) (hij : i ≠ j) :
    raiseDegree (raiseDegree d i) j = raiseDegree (raiseDegree d j) i := by
  have hij' : j ≠ i := Ne.symm hij
  have hg : ∀ (d : List ℕ) (i j : ℕ) (a : ℕ), i ≠ j → (d.set i a)[j]! = d[j]! := by
    intro d i j a hij
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hij,
      List.getElem!_eq_getElem?_getD]
  unfold raiseDegree
  rw [hg d i j _ hij,hg d j i _ hij']
  exact List.set_comm _ _ hij

/-- The PF6 discrete curl vanishes by its explicit quadratic potential. -/
lemma leadingIncrement_curl (Y : ℝ) (d : List ℕ) (i j : ℕ)
    (hi : i < d.length) (hj : j < d.length) (hij : i ≠ j) :
    leadingIncrement Y i d + leadingIncrement Y j (raiseDegree d i) =
      leadingIncrement Y j d + leadingIncrement Y i (raiseDegree d j) := by
  rw [leadingIncrement_eq_difference Y d i hi,
    leadingIncrement_eq_difference Y (raiseDegree d i) j (by simpa [raiseDegree_length] using hj),
    leadingIncrement_eq_difference Y d j hj,
    leadingIncrement_eq_difference Y (raiseDegree d j) i (by simpa [raiseDegree_length] using hi),
    raiseDegree_comm d i j hij]
  ring

lemma degreeCorrection_perm (Y : ℝ) (d e : List ℕ) (h : d.Perm e) :
    degreeCorrection d Y = degreeCorrection e Y := by
  unfold degreeCorrection
  rw [h.sum_eq,h.length_eq,(h.filter _).length_eq]

lemma leadingIncrement_path_sum (Y : ℝ) (v : ℕ → List ℕ) (i : ℕ → ℕ) (n : ℕ)
    (hi : ∀ s < n, i s < (v s).length)
    (hv : ∀ s < n, v (s+1) = raiseDegree (v s) (i s)) :
    ∑ s ∈ Finset.range n, leadingIncrement Y (i s) (v s) =
      degreeCorrection (v n) Y-degreeCorrection (v 0) Y := by
  calc
    _ = ∑ s ∈ Finset.range n, (degreeCorrection (v (s+1)) Y-degreeCorrection (v s) Y) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hv s (Finset.mem_range.mp hs),leadingIncrement_eq_difference Y (v s) (i s) (hi s (Finset.mem_range.mp hs))]
    _ = _ := Finset.sum_range_sub (fun s => degreeCorrection (v s) Y) n

lemma adjacentCoefficient_one_base (P : PsiTheory) (Y : ℝ) (i : ℕ) (d : List ℕ) :
    adjacentCoefficient P Y baseJet 1 i d =
      -(A Y*(∑ j ∈ Finset.range (d.eraseIdx i).length,
        (2*((d.eraseIdx i)[j]! : ℝ)+1)*
          ∑' l : ℕ, if 1 ≤ d[i]!+(d.eraseIdx i)[j]!+l then weight Y l else 0) +
       2*A Y*(∑' l : ℕ, weight Y l*(d[i]!+l-1 : ℕ))) := by
  have hsep : separatingSeries P Y baseJet 1 (d[i]!) (d.eraseIdx i) = 0 := by
    unfold separatingSeries
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro I hI
    have h : ¬ (Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ 1) := by omega
    simp [h]
  unfold adjacentCoefficient
  dsimp only
  rw [hsep,add_zero,map_add]
  congr 1
  congr 1
  · simp [mergerSeries,baseJet,PowerSeries.coeff_one_mul,shiftVariable_one,
      coefficientSum,coeff_zero_eq_constantCoeff,apply_ite]
  · simp [nonseparatingSeries,baseJet,PowerSeries.coeff_one_mul,shiftVariable_one,
      coefficientSum,coeff_zero_eq_constantCoeff,apply_ite]

lemma kernel_summable_zero_one (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    Summable (weight Y) ∧ Summable (fun l : ℕ => (l:ℝ)*weight Y l) := by
  obtain ⟨C₀,h₀⟩ := uniform_kernel_moments.2 0
  obtain ⟨C₁,h₁⟩ := uniform_kernel_moments.2 1
  have hw : Summable (weight Y) := by simpa using (h₀ Y hY).1
  refine ⟨hw, ?_⟩
  convert ((h₁ Y hY).1.sub hw) using 1
  ext l
  ring

lemma weight_zero_eq_one (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) : weight Y 0 = 1 := by
  obtain ⟨C,hC⟩ := uniform_kernel_moments.1
  simp [weight,(hC Y hY).1]

lemma merger_kernel_sum (Y : ℝ) (hw : Summable (weight Y)) (t a : ℕ) :
    (∑' l : ℕ, if 1 ≤ t+a+l then weight Y l else 0) =
      Theta Y - if t = 0 ∧ a = 0 then weight Y 0 else 0 := by
  by_cases h : t = 0 ∧ a = 0
  · rcases h with ⟨rfl,rfl⟩
    have he : (fun l : ℕ => if 1 ≤ 0+0+l then weight Y l else 0) =
      fun l => if l = 0 then 0 else weight Y l := by
      funext l
      split_ifs <;> simp_all <;> omega
    rw [he]
    have hs := hw.tsum_eq_add_tsum_ite 0
    simpa [Theta] using (eq_sub_iff_add_eq.mpr (by linarith :
      (∑' l : ℕ, if l = 0 then 0 else weight Y l)+weight Y 0 = ∑' l : ℕ, weight Y l))
  · have hp : ∀ l : ℕ, 1 ≤ t+a+l := by omega
    simp [hp,h,Theta]

lemma pair_kernel_sum (Y : ℝ) (hw : Summable (weight Y))
    (hm : Summable (fun l : ℕ => (l:ℝ)*weight Y l)) (t : ℕ) :
    (∑' l : ℕ, weight Y l*(t+l-1 : ℕ)) =
      ((t:ℝ)-1)*Theta Y+moment₁ Y+if t = 0 then weight Y 0 else 0 := by
  by_cases ht : t = 0
  · subst t
    have he : (fun l : ℕ => weight Y l*(0+l-1 : ℕ)) =
        fun l : ℕ => (l:ℝ)*weight Y l-weight Y l+if l = 0 then weight Y 0 else 0 := by
      funext l
      cases l with
      | zero => simp
      | succ l => push_cast; simp only [Nat.zero_add,Nat.add_sub_cancel,ite_false,Nat.succ_ne_zero]; ring
    rw [he]
    have hs : Summable (fun l : ℕ => if l = 0 then weight Y 0 else 0) := (hasSum_ite_eq 0 _).summable
    rw [(hm.sub hw).tsum_add hs,hm.tsum_sub hw]
    simp [Theta,moment₁]
    ring
  · have he : (fun l : ℕ => weight Y l*(t+l-1 : ℕ)) =
        fun l => ((t:ℝ)-1)*weight Y l+(l:ℝ)*weight Y l := by
      funext l
      have he : t+l-1 = (t-1)+l := by omega
      have hc : ((t-1:ℕ):ℝ) = (t:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ t)]; norm_num
      rw [he,Nat.cast_add,hc]
      ring
    rw [he,(hw.mul_left ((t:ℝ)-1)).tsum_add hm,tsum_mul_left]
    simp [ht,Theta,moment₁]

lemma zeros_add_positiveCount (d : List ℕ) : zeros d + positiveCount d = d.length := by
  induction d with
  | nil => simp [zeros,positiveCount]
  | cons a d ih =>
    by_cases ha : a = 0
    · simpa [zeros,positiveCount,ha,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using congrArg Nat.succ ih
    · have hp : 0 < a := Nat.pos_of_ne_zero ha
      simpa [zeros,positiveCount,ha,hp,Nat.add_assoc] using congrArg Nat.succ ih

lemma merger_finite_sum (t : ℕ) (d : List ℕ) (T : ℝ) :
    (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*(T-if t = 0 ∧ d[j]! = 0 then 1 else 0)) =
      T*(2*(d.sum:ℝ)+d.length)-if t = 0 then (zeros d:ℝ) else 0 := by
  induction d with
  | nil => simp [zeros]
  | cons a d ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    simp only [List.getElem!_cons_zero,List.getElem!_cons_succ]
    rw [ih]
    by_cases ht : t = 0 <;> by_cases ha : a = 0 <;>
      simp [ht,ha,zeros,Nat.cast_add] <;> ring

lemma adjacentCoefficient_one_closed (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀)
    (i : ℕ) (d : List ℕ) (hi : i < d.length) :
    adjacentCoefficient P Y baseJet 1 i d = -leadingIncrement Y i d := by
  obtain ⟨hw,hm⟩ := kernel_summable_zero_one Y hY
  rw [adjacentCoefficient_one_base]
  simp_rw [merger_kernel_sum Y hw,weight_zero_eq_one Y hY]
  rw [merger_finite_sum,pair_kernel_sum Y hw hm,weight_zero_eq_one Y hY]
  have hp : (d[i]! :: d.eraseIdx i).Perm d := by
    have he : d[i]! = d[i] := by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simpa only [he] using List.getElem_cons_eraseIdx_perm hi
  have hs := hp.sum_eq
  have hl := hp.length_eq
  have hq := (hp.filter (fun k => 0 < k)).length_eq
  have hz := zeros_add_positiveCount (d.eraseIdx i)
  simp only [List.sum_cons,List.length_cons] at hs hl
  unfold leadingIncrement
  by_cases ht : d[i]! = 0
  · simp only [ht,ite_true,zero_add,List.filter_cons,decide_false,ite_false] at hq ⊢
    change positiveCount (d.eraseIdx i) = positiveCount d at hq
    have hc : (zeros (d.eraseIdx i):ℝ)+(positiveCount d:ℝ) = (d.eraseIdx i).length := by
      exact_mod_cast (hq ▸ hz)
    have hsc : (d.sum:ℝ) = (d.eraseIdx i).sum := by exact_mod_cast (by simpa [ht] using hs.symm)
    have hlc : (d.length:ℝ) = (d.eraseIdx i).length+1 := by exact_mod_cast hl.symm
    rw [hsc,hlc]
    have hzc : (zeros (d.eraseIdx i):ℝ) = (d.eraseIdx i).length-(positiveCount d:ℝ) := by linarith
    rw [hzc]
    ring
  · simp only [ht,ite_false]
    have hsc : (d.sum:ℝ) = (d[i]!:ℝ)+(d.eraseIdx i).sum := by exact_mod_cast hs.symm
    have hlc : (d.length:ℝ) = (d.eraseIdx i).length+1 := by exact_mod_cast hl.symm
    rw [hsc,hlc]
    ring

lemma beforeCoordinate_length (d : List ℕ) (i t : ℕ) :
    (beforeCoordinate d i t).length = d.length := by simp [beforeCoordinate]

lemma beforeCoordinate_self (d : List ℕ) (i t : ℕ) (hi : i < d.length) :
    (beforeCoordinate d i t)[i]! = t := by
  simp [beforeCoordinate,List.getElem?_ofFn,hi]

lemma raiseDegree_beforeCoordinate (d : List ℕ) (i t : ℕ) (hi : i < d.length) :
    raiseDegree (beforeCoordinate d i t) i = beforeCoordinate d i (t+1) := by
  unfold raiseDegree
  rw [beforeCoordinate_self d i t hi]
  apply List.ext_getElem (by simp [beforeCoordinate])
  intro j hj₁ hj₂
  simp only [List.getElem_set,beforeCoordinate,List.getElem_ofFn]
  by_cases hji : j = i
  · subst j
    simp
  · have hij : i ≠ j := Ne.symm hji
    simp [hji,hij]

lemma beforeCoordinate_next (d : List ℕ) (i : ℕ) (hi : i < d.length) :
    beforeCoordinate d i (d[i]!) = beforeCoordinate d (i+1) 0 := by
  apply List.ext_getElem (by simp [beforeCoordinate])
  intro j hj₁ hj₂
  simp only [beforeCoordinate,List.getElem_ofFn]
  by_cases hji : j < i
  · simp [hji,show j < i+1 by omega]
  · by_cases he : j = i
    · subst j; simp
    · have hnext : ¬ j < i+1 := by omega
      have hne : j ≠ i+1 ∨ j = i+1 := by omega
      simp [hji,he,hnext]

lemma beforeCoordinate_zero (d : List ℕ) :
    beforeCoordinate d 0 0 = List.replicate d.length 0 := by
  apply List.ext_getElem (by simp [beforeCoordinate])
  intro j hj₁ hj₂
  simp [beforeCoordinate]

lemma beforeCoordinate_end (d : List ℕ) : beforeCoordinate d d.length 0 = d := by
  apply List.ext_getElem (by simp [beforeCoordinate])
  intro j hj₁ hj₂
  simp [beforeCoordinate,hj₂,List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hj₂]

lemma degreeCorrection_zero_tuple (Y : ℝ) (p : ℕ) :
    degreeCorrection (List.replicate p 0) Y = 0 := by
  simp [degreeCorrection,List.filter_replicate]

lemma profileAtOrder_one (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (d : List ℕ) :
    profileAtOrder P Y baseJet 1 d = -degreeCorrection d Y := by
  unfold profileAtOrder
  have hrow (i : ℕ) (hi : i < d.length) :
      (∑ t ∈ Finset.range d[i]!, adjacentCoefficient P Y baseJet 1 i (beforeCoordinate d i t)) =
        degreeCorrection (beforeCoordinate d i 0) Y-degreeCorrection (beforeCoordinate d (i+1) 0) Y := by
    have ha (t : ℕ) := adjacentCoefficient_one_closed P Y hY i (beforeCoordinate d i t)
      (by simpa [beforeCoordinate_length] using hi)
    simp_rw [ha]
    rw [Finset.sum_neg_distrib]
    have hs := leadingIncrement_path_sum Y (fun t => beforeCoordinate d i t) (fun _ => i) (d[i]!)
      (fun t ht => by simpa [beforeCoordinate_length] using hi)
      (fun t ht => (raiseDegree_beforeCoordinate d i t hi).symm)
    rw [hs,beforeCoordinate_next d i hi]
    ring
  calc
    _ = ∑ i ∈ Finset.range d.length,
        (degreeCorrection (beforeCoordinate d i 0) Y-degreeCorrection (beforeCoordinate d (i+1) 0) Y) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i (Finset.mem_range.mp hi)
    _ = degreeCorrection (beforeCoordinate d 0 0) Y-degreeCorrection (beforeCoordinate d d.length 0) Y :=
      Finset.sum_range_sub' (fun i => degreeCorrection (beforeCoordinate d i 0) Y) d.length
    _ = _ := by rw [beforeCoordinate_zero,beforeCoordinate_end,degreeCorrection_zero_tuple]; ring

/-- The first canonical triangular coefficient is exactly −δ_p. -/
lemma profileCoefficient_one (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (d : List ℕ) :
    profileCoefficient P Y d 1 = -degreeCorrection d Y := by
  change PowerSeries.coeff 1 (setCoeff (baseJet.profile d) 1 (profileAtOrder P Y baseJet 1 d)) = _
  rw [setCoeff_same,profileAtOrder_one P Y hY]

lemma profileCoefficient_one_perm (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀)
    (d e : List ℕ) (h : d.Perm e) : profileCoefficient P Y d 1 = profileCoefficient P Y e 1 := by
  rw [profileCoefficient_one P Y hY,profileCoefficient_one P Y hY,degreeCorrection_perm Y d e h]

/-- The actual first-order FE3 increments have vanishing discrete curl. -/
lemma adjacentCoefficient_one_curl (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀)
    (d : List ℕ) (i j : ℕ) (hi : i < d.length) (hj : j < d.length) (hij : i ≠ j) :
    adjacentCoefficient P Y baseJet 1 i d +
        adjacentCoefficient P Y baseJet 1 j (raiseDegree d i) =
      adjacentCoefficient P Y baseJet 1 j d +
        adjacentCoefficient P Y baseJet 1 i (raiseDegree d j) := by
  rw [adjacentCoefficient_one_closed P Y hY i d hi,
    adjacentCoefficient_one_closed P Y hY j (raiseDegree d i)
      (by simpa [raiseDegree_length] using hj),
    adjacentCoefficient_one_closed P Y hY j d hj,
    adjacentCoefficient_one_closed P Y hY i (raiseDegree d j)
      (by simpa [raiseDegree_length] using hi)]
  linear_combination -(leadingIncrement_curl Y d i j hi hj hij)

/-- The actual first-order coefficient sum along any coordinate path depends
only on its endpoint values of δ_p. -/
lemma adjacentCoefficient_one_path_sum (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀)
    (v : ℕ → List ℕ) (i : ℕ → ℕ) (n : ℕ)
    (hi : ∀ s < n, i s < (v s).length)
    (hv : ∀ s < n, v (s+1) = raiseDegree (v s) (i s)) :
    (∑ s ∈ Finset.range n, adjacentCoefficient P Y baseJet 1 (i s) (v s)) =
      degreeCorrection (v 0) Y-degreeCorrection (v n) Y := by
  calc
    _ = ∑ s ∈ Finset.range n, -leadingIncrement Y (i s) (v s) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact adjacentCoefficient_one_closed P Y hY (i s) (v s) (hi s (Finset.mem_range.mp hs))
    _ = _ := by
      rw [Finset.sum_neg_distrib,leadingIncrement_path_sum Y v i n hi hv]
      ring

/-- Arbitrary admissible coordinate paths with the same endpoints give the
same actual first-order coefficient. This assumes only that the steps form paths. -/
lemma adjacentCoefficient_one_path_independent (P : PsiTheory) (Y : ℝ)
    (hY : Y ∈ Set.Icc 0 y₀) (v u : ℕ → List ℕ) (i j : ℕ → ℕ) (n m : ℕ)
    (hi : ∀ s < n, i s < (v s).length) (hj : ∀ s < m, j s < (u s).length)
    (hv : ∀ s < n, v (s+1) = raiseDegree (v s) (i s))
    (hu : ∀ s < m, u (s+1) = raiseDegree (u s) (j s))
    (hstart : v 0 = u 0) (hend : v n = u m) :
    (∑ s ∈ Finset.range n, adjacentCoefficient P Y baseJet 1 (i s) (v s)) =
      ∑ s ∈ Finset.range m, adjacentCoefficient P Y baseJet 1 (j s) (u s) := by
  rw [adjacentCoefficient_one_path_sum P Y hY v i n hi hv,
    adjacentCoefficient_one_path_sum P Y hY u j m hj hu,hstart,hend]

end WP.HigherOrder
