import WPFormalization.Volumes.BoundaryPolynomial
noncomputable section
set_option maxHeartbeats 0
namespace WP

lemma shifted_perm (P : PsiTheory) (g : ℕ) {d e : List ℕ} (hp : d.Perm e) (Y : ℝ) :
    shifted P g d Y = shifted P g e Y := by
  have hlen := hp.length_eq
  have hsum := hp.sum_eq
  have hdef : deficit g d = deficit g e := by simp only [deficit, hlen, hsum]
  have hprod := (hp.map (fun k => (oddFactorial k : ℝ))).prod_eq
  have hpsi (l : List ℕ) : pure P g (d++l) = pure P g (e++l) :=
    P.symmetry g _ _ ((hp.append_right l).map Int.ofNat)
  unfold shifted
  rw [hdef]
  simp only [hlen, hsum, hprod, hpsi]

lemma mixedBracket_perm (P : PsiTheory) (g : ℕ) {d e : List ℕ} (hp : d.Perm e) :
    mixedBracket P g d = mixedBracket P g e := by
  simp only [mixedBracket, hp.sum_eq, deficit, hp.length_eq, shifted_perm P g hp]

lemma boundaryVolumeModel_equiv (P : PsiTheory) (g n : ℕ) (L : Fin n → ℝ)
    (e : Equiv.Perm (Fin n)) :
    boundaryVolumeModel P g n (L ∘ e) = boundaryVolumeModel P g n L := by
  classical
  unfold boundaryVolumeModel
  apply Finset.sum_bij (fun d _ => d ∘ e.symm)
  · intro d hd
    rw [mem_degreeTuples_iff] at hd ⊢
    simpa only [Function.comp_def, Equiv.sum_comp e.symm d] using hd
  · intro d hd d' hd' he
    funext i
    have hi := congrFun he (e i)
    simpa only [Function.comp_def, e.symm_apply_apply] using hi
  · intro d hd
    refine ⟨d ∘ e,?_,?_⟩
    · rw [mem_degreeTuples_iff] at hd ⊢
      simpa only [Function.comp_def, Equiv.sum_comp e d] using hd
    · ext i
      simp
  · intro d hd
    have hm := mixedBracket_perm P g (Equiv.Perm.ofFn_comp_perm e.symm d)
    rw [←hm]
    congr 1
    symm
    convert Equiv.prod_comp e.symm (fun i => (L ∘ e) i^(2*d i)/((4:ℝ)^(d i)*(2*d i+1).factorial)) using 1 <;>
      simp [Function.comp_def]

lemma boundaryVolumeModel_reindex (P : PsiTheory) (g n m : ℕ) (L : Fin m → ℝ)
    (e : Fin n ≃ Fin m) :
    boundaryVolumeModel P g n (L ∘ e) = boundaryVolumeModel P g m L := by
  have hnm : n = m := by simpa using Fintype.card_congr e
  subst m
  exact boundaryVolumeModel_equiv P g n L e

lemma boundaryVolumeModel_append_comm (P : PsiTheory) (g n m : ℕ)
    (L : Fin n → ℝ) (M : Fin m → ℝ) :
    boundaryVolumeModel P g (n+m) (Fin.append L M) =
      boundaryVolumeModel P g (m+n) (Fin.append M L) := by
  have hfun : (Fin.append M L) ∘ (finAddFlip : Fin (n+m) ≃ Fin (m+n)) = Fin.append L M := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Function.comp_def]
  rw [←hfun]
  exact boundaryVolumeModel_reindex P g (n+m) (m+n) (Fin.append M L) finAddFlip

lemma boundaryVolumeModel_zero_prefix_eq_suffix (P : PsiTheory) (g q p : ℕ)
    (L : Fin p → ℝ) :
    boundaryVolumeModel P g (q+p) (Fin.append (fun _ : Fin q => 0) L) =
      boundaryVolumeModel P g (p+q) (Fin.append L (fun _ : Fin q => 0)) :=
  boundaryVolumeModel_append_comm P g q p (fun _ => 0) L
end WP
