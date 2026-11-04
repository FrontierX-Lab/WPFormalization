import WPFormalization.HigherOrder.BoundaryAffineMoment
import WPFormalization.HigherOrder.MultivariatePowerSums
/-! Boundary-stratified finite summation along the actual canonical coordinate path. Low upper limits are evaluated finitely; high limits retain all low-index corrections. A genuine adjacent-edge joint certificate yields the canonical profile coefficient, with degree increasing by at most one. No arbitrary-path compatibility is assumed. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def headSlot {p : ℕ} (u : MvPolynomial (Fin p) R)
    (F : MvPolynomial (Fin (p + 1)) R) : MvPolynomial (Fin p) R :=
  F.eval₂ MvPolynomial.C (Fin.cases u MvPolynomial.X)

lemma headSlot_degree {p : ℕ} (u : MvPolynomial (Fin p) R)
    (F : MvPolynomial (Fin (p + 1)) R) (hu : u.totalDegree ≤ 1) :
    (headSlot u F).totalDegree ≤ F.totalDegree := by
  apply linear_mv_substitution_degree
  intro i
  refine Fin.cases hu (fun j => variable_degree_le_one j) i

lemma headSlot_eval {p : ℕ} (u : MvPolynomial (Fin p) R)
    (F : MvPolynomial (Fin (p + 1)) R) (x : Fin p → R) :
    MvPolynomial.eval x (headSlot u F) =
      MvPolynomial.eval (Fin.cases (MvPolynomial.eval x u) x) F := by
  have he := MvPolynomial.eval₂_comp_left (MvPolynomial.eval x) MvPolynomial.C
    (Fin.cases u MvPolynomial.X) F
  have hc : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id R := by ext a; simp
  have hx : (MvPolynomial.eval x ∘ Fin.cases u MvPolynomial.X) =
      Fin.cases (MvPolynomial.eval x u) x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  change MvPolynomial.eval x (F.eval₂ MvPolynomial.C _) =
    MvPolynomial.eval₂ (RingHom.id R) _ F
  simpa only [hc, hx] using he

def stepTemplate {p : ℕ} (b B : ℕ) (σ : Fin p → Option (Fin (B + 1)))
    (F : (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R)
    (t : ℕ) : MvPolynomial (Fin (p + 1)) R :=
  F (Fin.cases (classify 1 b (fun _ => t) 0) (classify p b (representative p B σ)))

def highStepTemplate {p : ℕ} (b B : ℕ) (σ : Fin p → Option (Fin (B + 1)))
    (F : (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R) :
    MvPolynomial (Fin (p + 1)) R :=
  F (Fin.cases none (classify p b (representative p B σ)))

def boundaryIntegratedPolynomial {p : ℕ} (b B : ℕ) (σ : Fin p → Option (Fin (B + 1)))
    (i : Fin p)
    (F : (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R) :
    MvPolynomial (Fin p) R :=
  match σ i with
  | some k => ∑ t ∈ Finset.range k.val,
      headSlot (MvPolynomial.C (t : R)) (stepTemplate b B σ F t)
  | none => headSlot (MvPolynomial.X i)
      (BoundaryPolynomial.firstVariableSumPolynomial (highStepTemplate b B σ F)) +
      ∑ t ∈ Finset.range (b + 1),
        (headSlot (MvPolynomial.C (t : R)) (stepTemplate b B σ F t) -
          headSlot (MvPolynomial.C (t : R)) (highStepTemplate b B σ F))

lemma boundaryIntegratedPolynomial_degree {p : ℕ} (b B D : ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (i : Fin p)
    (F : (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R)
    (hdegree : ∀ τ, (F τ).totalDegree ≤ D) :
    (boundaryIntegratedPolynomial b B σ i F).totalDegree ≤ D + 1 := by
  have hstep (t : ℕ) : (headSlot (MvPolynomial.C (t : R)) (stepTemplate b B σ F t)).totalDegree ≤ D :=
    (headSlot_degree _ _ (by rw [MvPolynomial.totalDegree_C]; omega)).trans (hdegree _)
  have hhigh (t : ℕ) : (headSlot (MvPolynomial.C (t : R)) (highStepTemplate b B σ F)).totalDegree ≤ D :=
    (headSlot_degree _ _ (by rw [MvPolynomial.totalDegree_C]; omega)).trans (hdegree _)
  unfold boundaryIntegratedPolynomial
  split
  · apply (MvPolynomial.totalDegree_finsetSum_le (fun t ht => hstep t)).trans
    omega
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le _ ?_
    · have hH : (highStepTemplate b B σ F).totalDegree ≤ D := hdegree _
      exact ((headSlot_degree _ _ (variable_degree_le_one _)).trans
        (BoundaryPolynomial.firstVariableSumPolynomial_degree _)).trans (Nat.add_le_add_right hH 1)
    · apply MvPolynomial.totalDegree_finsetSum_le
      intro t ht
      exact ((MvPolynomial.totalDegree_sub _ _).trans (max_le (hstep t) (hhigh t))).trans (by omega)

lemma cast_cons_ring {p : ℕ} (n : ℕ) (d : Fin p → ℕ) :
    (fun i : Fin (p + 1) => ((Fin.cases n d i : ℕ) : R)) =
      Fin.cases (n : R) (fun i => (d i : R)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma stepTemplate_eval {p : ℕ} (b B : ℕ) (hb : b ≤ B) (d : Fin p → ℕ)
    (F : (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R) (t : ℕ) :
    MvPolynomial.eval (fun j => (d j : R))
      (headSlot (MvPolynomial.C (t : R)) (stepTemplate b B (classify p B d) F t)) =
      profileRecipeValue b F (Fin.cases t d) := by
  rw [headSlot_eval, MvPolynomial.eval_C, stepTemplate, classify_representative b B hb d]
  unfold profileRecipeValue
  rw [classify_cons, cast_cons_ring]

lemma boundaryIntegratedPolynomial_eval {p : ℕ} (b B : ℕ) (hb : b ≤ B)
    (d : Fin p → ℕ) (i : Fin p)
    (F : (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R) :
    MvPolynomial.eval (fun j => (d j : R))
      (boundaryIntegratedPolynomial b B (classify p B d) i F) =
      ∑ t ∈ Finset.range (d i), profileRecipeValue b F (Fin.cases t d) := by
  let H := highStepTemplate b B (classify p B d) F
  let x : Fin p → R := fun j => (d j : R)
  let v : ℕ → R := fun t => profileRecipeValue b F (Fin.cases t d)
  let w : ℕ → R := fun t => MvPolynomial.eval (Fin.cases (t : R) x) H
  have hstep (t : ℕ) : MvPolynomial.eval x
      (headSlot (MvPolynomial.C (t : R)) (stepTemplate b B (classify p B d) F t)) = v t :=
    stepTemplate_eval b B hb d F t
  dsimp only [x] at hstep
  by_cases hi : d i ≤ B
  · have hs : classify p B d i = some (⟨d i, by omega⟩ : Fin (B + 1)) := by
      simp only [classify, dite_eq_left hi]
    unfold boundaryIntegratedPolynomial
    rw [hs]
    simp only [map_sum, hstep]
    rfl
  · have hs : classify p B d i = none := by simp only [classify, dite_eq_right hi]
    have hcorr : (∑ t ∈ Finset.range (d i), (v t - w t)) =
        ∑ t ∈ Finset.range (b + 1), (v t - w t) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro t hti htb
      have ht : b < t := by
        have hh : b + 1 ≤ t := by simpa only [Finset.mem_range, not_lt] using htb
        omega
      have he : v t = w t := by
        dsimp [v, w, H, highStepTemplate, profileRecipeValue, x]
        rw [classify_large_head b t d ht, cast_cons_ring, classify_representative b B hb d]
      rw [he, sub_self]
    unfold boundaryIntegratedPolynomial
    rw [hs]
    simp only [map_add, map_sum, map_sub, hstep]
    have hw (t : ℕ) : MvPolynomial.eval x (headSlot (MvPolynomial.C (t : R)) H) = w t := by
      rw [headSlot_eval, MvPolynomial.eval_C]
    have hsum : MvPolynomial.eval x
        (headSlot (MvPolynomial.X i) (BoundaryPolynomial.firstVariableSumPolynomial H)) =
        ∑ t ∈ Finset.range (d i), w t := by
      rw [headSlot_eval, MvPolynomial.eval_X]
      exact BoundaryPolynomial.firstVariableSumPolynomial_eval H (d i) x
    change MvPolynomial.eval x (headSlot (MvPolynomial.X i)
      (BoundaryPolynomial.firstVariableSumPolynomial H)) +
      (∑ t ∈ Finset.range (b + 1), (v t - MvPolynomial.eval x (headSlot (MvPolynomial.C (t : R)) H))) = _
    simp_rw [hw]
    rw [hsum, ← hcorr, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring


lemma map_eval_nat {p : ℕ} (φ : R →+* ℝ) (F : MvPolynomial (Fin p) R) (d : Fin p → ℕ) :
    φ (MvPolynomial.eval (fun j => (d j : R)) F) =
      MvPolynomial.eval₂ φ (fun j => (d j : ℝ)) F := by
  have he := MvPolynomial.eval₂_comp_left φ (RingHom.id R) (fun j => (d j : R)) F
  change φ (MvPolynomial.eval₂ (RingHom.id R) (fun j => (d j : R)) F) = _
  simpa only [RingHom.comp_id, Function.comp_def, map_natCast] using he

lemma boundaryIntegratedPolynomial_actual_eval {p : ℕ} (b B : ℕ) (hb : b ≤ B)
    (d : Fin p → ℕ) (i : Fin p)
    (F : (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R)
    (φ : R →+* ℝ) (f : (Fin (p + 1) → ℕ) → ℝ)
    (hactual : ∀ v : Fin (p + 1) → ℕ,
      f v = MvPolynomial.eval₂ φ (fun j => (v j : ℝ)) (F (classify (p + 1) b v))) :
    (∑ t ∈ Finset.range (d i), f (Fin.cases t d)) =
      MvPolynomial.eval₂ φ (fun j => (d j : ℝ))
        (boundaryIntegratedPolynomial b B (classify p B d) i F) := by
  rw [← map_eval_nat, boundaryIntegratedPolynomial_eval b B hb d i F, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [profileRecipeValue_eval]
  exact hactual _

def fixedPathPolynomial {p : ℕ} (b B : ℕ) (σ : Fin p → Option (Fin (B + 1)))
    (F : Fin p → (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R) :
    MvPolynomial (Fin p) R :=
  ∑ i : Fin p, boundaryIntegratedPolynomial b B σ i (F i)

lemma fixedPathPolynomial_degree {p : ℕ} (b B D : ℕ) (σ : Fin p → Option (Fin (B + 1)))
    (F : Fin p → (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R)
    (hdegree : ∀ i τ, (F i τ).totalDegree ≤ D) :
    (fixedPathPolynomial b B σ F).totalDegree ≤ D + 1 := by
  exact MvPolynomial.totalDegree_finsetSum_le (fun i hi =>
    boundaryIntegratedPolynomial_degree b B D σ i (F i) (hdegree i))


lemma canonical_profile_fixed_path_finite (P : PsiTheory) (Y : ℝ) (p k : ℕ)
    (d : Fin p → ℕ) :
    profileCoefficient P Y (List.ofFn d) (k + 1) =
      ∑ i : Fin p, ∑ t ∈ Finset.range (d i),
        adjacentCoefficient P Y (hierarchyJet P Y k) (k + 1) i.val
          (beforeCoordinate (List.ofFn d) i.val t) := by
  change PowerSeries.coeff (k + 1)
    (setCoeff ((hierarchyJet P Y k).profile (List.ofFn d)) (k + 1)
      (profileAtOrder P Y (hierarchyJet P Y k) (k + 1) (List.ofFn d))) = _
  rw [setCoeff_same]
  unfold profileAtOrder
  rw [List.length_ofFn, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (List.ofFn d)[i.val]! = d i := by simp
  rw [he]

lemma actual_canonical_profile_path_recipe (P : PsiTheory) (p k b B : ℕ) (hb : b ≤ B)
    (F : Fin p → (Fin (p + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 1)) R)
    (φ : ℝ → R →+* ℝ)
    (hactual : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ i : Fin p, ∀ v : Fin (p + 1) → ℕ,
      adjacentCoefficient P Y (hierarchyJet P Y k) (k + 1) i.val
          (beforeCoordinate (List.ofFn (fun j => v j.succ)) i.val (v 0)) =
        MvPolynomial.eval₂ (φ Y) (fun j => (v j : ℝ)) (F i (classify (p + 1) b v))) :
    ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ,
      profileCoefficient P Y (List.ofFn d) (k + 1) =
        MvPolynomial.eval₂ (φ Y) (fun j => (d j : ℝ))
          (fixedPathPolynomial b B (classify p B d) F) := by
  intro Y hY d
  rw [canonical_profile_fixed_path_finite, fixedPathPolynomial, MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Fin.cases_zero, Fin.cases_succ] using
    boundaryIntegratedPolynomial_actual_eval b B hb d i (F i) (φ Y)
      (fun v => adjacentCoefficient P Y (hierarchyJet P Y k) (k + 1) i.val
        (beforeCoordinate (List.ofFn (fun j => v j.succ)) i.val (v 0))) (hactual Y hY i)
end WP.HigherOrder.JointBoundary
