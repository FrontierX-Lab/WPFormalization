import WPFormalization.HigherOrder.BoundaryAffineStatus
import WPFormalization.HigherOrder.JointBoundaryPair
import WPFormalization.HigherOrder.PolynomialMomentContraction
/-! A current actual child profile-stratum certificate yields a joint parent polynomial for the genuine weighted affine head. The construction preserves degree D, uses moments only through D and low weights only through b+c, and fixes the parent cutoff before all degrees and the parameter. The all-order child certificates remain an inductive paper obligation. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma variable_degree_le_one {ι : Type*} (i : ι) :
    (MvPolynomial.X i : MvPolynomial ι R).totalDegree ≤ 1 := by
  change (MvPolynomial.monomial (Finsupp.single i 1) (1 : R)).totalDegree ≤ 1
  simpa using (MvPolynomial.totalDegree_monomial_le (Finsupp.single i 1) (1 : R))

def affineLiftAssignment {p q : ℕ} (a : Fin p → ℕ) (c : ℕ) (e : Fin q → Fin p) :
    Fin (q + 1) → MvPolynomial (Option (Fin p)) R :=
  Fin.cases
    (MvPolynomial.X none +
      (∑ i : Fin p, MvPolynomial.C (a i : R) * MvPolynomial.X (some i)) - MvPolynomial.C (c : R))
    (fun j => MvPolynomial.X (some (e j)))

def affineLift {p q : ℕ} (a : Fin p → ℕ) (c : ℕ) (e : Fin q → Fin p)
    (F : MvPolynomial (Fin (q + 1)) R) : MvPolynomial (Option (Fin p)) R :=
  F.eval₂ MvPolynomial.C (affineLiftAssignment a c e)

lemma affineLift_degree {p q : ℕ} (a : Fin p → ℕ) (c : ℕ) (e : Fin q → Fin p)
    (F : MvPolynomial (Fin (q + 1)) R) : (affineLift a c e F).totalDegree ≤ F.totalDegree := by
  apply linear_mv_substitution_degree
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le _ (by
      change (MvPolynomial.C (c : R) : MvPolynomial (Option (Fin p)) R).totalDegree ≤ 1
      rw [MvPolynomial.totalDegree_C]
      omega)
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le (variable_degree_le_one _) ?_
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact variable_degree_le_one _
  · exact variable_degree_le_one _

lemma affineLift_eval {p q : ℕ} (a : Fin p → ℕ) (c : ℕ) (e : Fin q → Fin p)
    (F : MvPolynomial (Fin (q + 1)) R) (φ : R →+* ℝ) (d : Fin p → ℕ) (l : ℕ) :
    MvPolynomial.eval₂ φ (fun i : Option (Fin p) => i.elim (l : ℝ) (fun j => (d j : ℝ)))
      (affineLift a c e F) =
      MvPolynomial.eval₂ φ
        (Fin.cases ((l : ℝ) + (∑ i : Fin p, (a i : ℝ) * (d i : ℝ)) - (c : ℝ))
          (fun j => (d (e j) : ℝ))) F := by
  let ψ : MvPolynomial (Option (Fin p)) R →+* ℝ :=
    MvPolynomial.eval₂Hom φ (fun i => i.elim (l : ℝ) (fun j => (d j : ℝ)))
  have he := MvPolynomial.eval₂_comp_left ψ MvPolynomial.C (affineLiftAssignment a c e) F
  have hc : ψ.comp MvPolynomial.C = φ := by ext x; simp [ψ]
  have hx : (ψ ∘ affineLiftAssignment a c e) =
      Fin.cases ((l : ℝ) + (∑ i : Fin p, (a i : ℝ) * (d i : ℝ)) - (c : ℝ))
        (fun j => (d (e j) : ℝ)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [affineLiftAssignment, ψ]
    · simp [affineLiftAssignment, ψ]
  change ψ (F.eval₂ MvPolynomial.C (affineLiftAssignment a c e)) = _
  simpa only [hc, hx] using he

def specializeMomentVariable {p : ℕ} (l : ℕ)
    (F : MvPolynomial (Option (Fin p)) R) : MvPolynomial (Fin p) R :=
  F.eval₂ MvPolynomial.C (fun i => i.elim (MvPolynomial.C (l : R)) MvPolynomial.X)

lemma specializeMomentVariable_degree {p : ℕ} (l : ℕ)
    (F : MvPolynomial (Option (Fin p)) R) :
    (specializeMomentVariable l F).totalDegree ≤ F.totalDegree := by
  apply linear_mv_substitution_degree
  intro i
  cases i with
  | none =>
      change (MvPolynomial.C (l : R) : MvPolynomial (Fin p) R).totalDegree ≤ 1
      rw [MvPolynomial.totalDegree_C]
      omega
  | some j => exact variable_degree_le_one _

lemma specializeMomentVariable_eval {p : ℕ} (l : ℕ)
    (F : MvPolynomial (Option (Fin p)) R) (φ : R →+* ℝ) (d : Fin p → ℕ) :
    MvPolynomial.eval₂ φ (fun i => (d i : ℝ)) (specializeMomentVariable l F) =
      MvPolynomial.eval₂ φ (fun i => i.elim (l : ℝ) (fun j => (d j : ℝ))) F := by
  let ψ : MvPolynomial (Fin p) R →+* ℝ := MvPolynomial.eval₂Hom φ (fun i => (d i : ℝ))
  have he := MvPolynomial.eval₂_comp_left ψ MvPolynomial.C
    (fun i : Option (Fin p) => i.elim (MvPolynomial.C (l : R)) MvPolynomial.X) F
  have hc : ψ.comp MvPolynomial.C = φ := by ext x; simp [ψ]
  have hx : (ψ ∘ fun i : Option (Fin p) => i.elim (MvPolynomial.C (l : R)) MvPolynomial.X) =
      (fun i => i.elim (l : ℝ) (fun j => (d j : ℝ))) := by
    funext i
    cases i <;> simp [ψ]
  change ψ (F.eval₂ MvPolynomial.C _) = _
  simpa only [hc, hx] using he


def affineTailPattern {p q : ℕ} (b B : ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p) :
    Fin q → Option (Fin (b + 1)) :=
  classify q b (fun j => representative p B σ (e j))

def affineHighLift {p q : ℕ} (b c B : ℕ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R) :
    MvPolynomial (Option (Fin p)) R :=
  affineLift a c e (F (Fin.cases none (affineTailPattern b B σ e)))

def affineLowPolynomial {p q : ℕ} (b c B : ℕ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (l : ℕ) : MvPolynomial (Fin p) R :=
  match affineHeadStatus b c (∑ i : Fin p, a i * representative p B σ i) l with
  | none => 0
  | some γ => specializeMomentVariable l
      (affineLift a c e (F (Fin.cases γ (affineTailPattern b B σ e))))

def affineMomentPolynomial {p q : ℕ} (b c B : ℕ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (M W : ℕ → R) : MvPolynomial (Fin p) R :=
  BoundaryPolynomial.momentContraction M (affineHighLift b c B a σ e F) +
    ∑ l ∈ Finset.range (b + c + 1), MvPolynomial.C (W l) *
      (affineLowPolynomial b c B a σ e F l -
        specializeMomentVariable l (affineHighLift b c B a σ e F))

lemma affineLowPolynomial_degree {p q : ℕ} (b c B D : ℕ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ τ, (F τ).totalDegree ≤ D) (l : ℕ) :
    (affineLowPolynomial b c B a σ e F l).totalDegree ≤ D := by
  unfold affineLowPolynomial
  split
  · simp
  · exact ((specializeMomentVariable_degree _ _).trans
      (affineLift_degree _ _ _ _)).trans (hdegree _)

lemma affineMomentPolynomial_degree {p q : ℕ} (b c B D : ℕ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ τ, (F τ).totalDegree ≤ D) (M W : ℕ → R) :
    (affineMomentPolynomial b c B a σ e F M W).totalDegree ≤ D := by
  have hh : (affineHighLift b c B a σ e F).totalDegree ≤ D :=
    (affineLift_degree _ _ _ _).trans (hdegree _)
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le ((BoundaryPolynomial.momentContraction_degree _ _).trans hh) ?_
  apply MvPolynomial.totalDegree_finsetSum_le
  intro l hl
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_sub _ _).trans
    (max_le (affineLowPolynomial_degree b c B D a σ e F hdegree l)
      ((specializeMomentVariable_degree _ _).trans hh))

lemma affineTailPattern_classify {p q : ℕ} (b B : ℕ) (hb : b ≤ B)
    (d : Fin p → ℕ) (e : Fin q → Fin p) :
    affineTailPattern b B (classify p B d) e = classify q b (fun j => d (e j)) := by
  funext j
  have he := congrFun (classify_representative b B hb d) (e j)
  exact he

lemma affine_real_head {p : ℕ} (a d : Fin p → ℕ) (c l : ℕ)
    (hc : c ≤ (∑ i : Fin p, a i * d i) + l) :
    (l : ℝ) + (∑ i : Fin p, (a i : ℝ) * (d i : ℝ)) - (c : ℝ) =
      (((∑ i : Fin p, a i * d i) + l - c : ℕ) : ℝ) := by
  rw [Nat.cast_sub hc, Nat.cast_add, Nat.cast_sum]
  simp only [Nat.cast_mul]
  ring


lemma classify_cons {p : ℕ} (b n : ℕ) (tail : Fin p → ℕ) :
    classify (p + 1) b (Fin.cases n tail) =
      Fin.cases (classify 1 b (fun _ => n) 0) (classify p b tail) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma cast_cons {p : ℕ} (n : ℕ) (tail : Fin p → ℕ) :
    (fun i : Fin (p + 1) => ((Fin.cases n tail i : ℕ) : ℝ)) =
      Fin.cases (n : ℝ) (fun i => (tail i : ℝ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma affineLowPolynomial_eval {p q : ℕ} (b c B : ℕ) (hB : b + c ≤ B)
    (a d : Fin p → ℕ) (e : Fin q → Fin p)
    (F : (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (φ : R →+* ℝ) (f : (Fin (q + 1) → ℕ) → ℝ)
    (hactual : ∀ v : Fin (q + 1) → ℕ,
      f v = MvPolynomial.eval₂ φ (fun i => (v i : ℝ)) (F (classify (q + 1) b v))) (l : ℕ) :
    MvPolynomial.eval₂ φ (fun i => (d i : ℝ))
        (affineLowPolynomial b c B a (classify p B d) e F l) =
      if c ≤ (∑ i : Fin p, a i * d i) + l then
        f (Fin.cases ((∑ i : Fin p, a i * d i) + l - c) (fun j => d (e j))) else 0 := by
  unfold affineLowPolynomial
  rw [← affineHeadStatus_eq_representative b c B l hB a d]
  by_cases hc : c ≤ (∑ i : Fin p, a i * d i) + l
  · simp only [affineHeadStatus, ite_eq_left hc]
    rw [specializeMomentVariable_eval, affineLift_eval, affine_real_head a d c l hc,
      affineTailPattern_classify b B (by omega) d e, hactual, classify_cons, cast_cons]
    rfl
  · simp only [affineHeadStatus, ite_eq_right hc, MvPolynomial.eval₂_zero]

lemma affineHighLift_eval_tail {p q : ℕ} (b c B : ℕ) (hB : b + c ≤ B)
    (a d : Fin p → ℕ) (e : Fin q → Fin p)
    (F : (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (φ : R →+* ℝ) (f : (Fin (q + 1) → ℕ) → ℝ)
    (hactual : ∀ v : Fin (q + 1) → ℕ,
      f v = MvPolynomial.eval₂ φ (fun i => (v i : ℝ)) (F (classify (q + 1) b v)))
    (l : ℕ) (hl : b + c + 1 ≤ l) :
    MvPolynomial.eval₂ φ (fun i => i.elim (l : ℝ) (fun j => (d j : ℝ)))
        (affineHighLift b c B a (classify p B d) e F) =
      if c ≤ (∑ i : Fin p, a i * d i) + l then
        f (Fin.cases ((∑ i : Fin p, a i * d i) + l - c) (fun j => d (e j))) else 0 := by
  have hc : c ≤ (∑ i : Fin p, a i * d i) + l := by omega
  have hn : b < (∑ i : Fin p, a i * d i) + l - c := by omega
  rw [ite_eq_left hc, affineHighLift, affineLift_eval, affine_real_head a d c l hc,
    affineTailPattern_classify b B (by omega) d e, hactual,
    classify_large_head b _ _ hn, cast_cons]

lemma affineMomentPolynomial_hasSum {p q : ℕ} (b c B D : ℕ) (hB : b + c ≤ B)
    (a d : Fin p → ℕ) (e : Fin q → Fin p)
    (F : (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ τ, (F τ).totalDegree ≤ D)
    (φ : R →+* ℝ) (f : (Fin (q + 1) → ℕ) → ℝ)
    (hactual : ∀ v : Fin (q + 1) → ℕ,
      f v = MvPolynomial.eval₂ φ (fun i => (v i : ℝ)) (F (classify (q + 1) b v)))
    (M W : ℕ → R) (w : ℕ → ℝ)
    (hm : ∀ k : ℕ, k ≤ D → HasSum (fun l : ℕ => (l : ℝ) ^ k * w l) (φ (M k)))
    (hw : ∀ l : ℕ, l < b + c + 1 → w l = φ (W l)) :
    HasSum (fun l : ℕ => w l *
      (if c ≤ (∑ i : Fin p, a i * d i) + l then
        f (Fin.cases ((∑ i : Fin p, a i * d i) + l - c) (fun j => d (e j))) else 0))
      (MvPolynomial.eval₂ φ (fun i => (d i : ℝ))
        (affineMomentPolynomial b c B a (classify p B d) e F M W)) := by
  let H := affineHighLift b c B a (classify p B d) e F
  let v : ℕ → ℝ := fun l =>
    if c ≤ (∑ i : Fin p, a i * d i) + l then
      f (Fin.cases ((∑ i : Fin p, a i * d i) + l - c) (fun j => d (e j))) else 0
  let x : Fin p → ℝ := fun i => (d i : ℝ)
  let Hval : ℕ → ℝ := fun l =>
    MvPolynomial.eval₂ φ (fun i => i.elim (l : ℝ) x) H
  have hdeg : H.totalDegree ≤ D := (affineLift_degree _ _ _ _).trans (hdegree _)
  have hsum := BoundaryPolynomial.momentContraction_hasSum M H φ x w D hdeg hm
  have hcorr : HasSum (fun l : ℕ => w l * (v l - Hval l))
      (∑ l ∈ Finset.range (b + c + 1), w l * (v l - Hval l)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro l hl
    have hl' : b + c + 1 ≤ l := by simpa only [Finset.mem_range, not_lt] using hl
    have he := affineHighLift_eval_tail b c B hB a d e F φ f hactual l hl'
    change w l * (v l - Hval l) = 0
    change Hval l = v l at he
    rw [he, sub_self, mul_zero]
  have hh := hsum.add hcorr
  convert! hh using 1
  · funext l
    change w l * v l = w l * Hval l + w l * (v l - Hval l)
    ring
  · simp only [affineMomentPolynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sum,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_sub]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [hw l (Finset.mem_range.mp hl), specializeMomentVariable_eval,
      affineLowPolynomial_eval b c B hB a d e F φ f hactual l]


lemma actual_profile_affine_moment_recipe (P : PsiTheory) (p q K b c B D : ℕ)
    (hB : b + c ≤ B) (a : Fin p → ℕ) (e : Fin q → Fin p)
    (F : (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ τ, (F τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ v : Fin (q + 1) → ℕ,
      profileCoefficient P Y (List.ofFn v) K =
        MvPolynomial.eval₂ (φ Y) (fun i => (v i : ℝ)) (F (classify (q + 1) b v)))
    (M W : ℕ → R) (w : ℝ → ℕ → ℝ)
    (hm : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * w Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ l : ℕ, l < b + c + 1 → w Y l = (φ Y) (W l)) :
    ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ,
      HasSum (fun l : ℕ => w Y l *
        (if c ≤ (∑ i : Fin p, a i * d i) + l then
          profileCoefficient P Y
            (((∑ i : Fin p, a i * d i) + l - c) :: List.ofFn (fun j => d (e j))) K else 0))
        (MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ))
          (affineMomentPolynomial b c B a (classify p B d) e F M W)) := by
  intro Y hY d
  simpa only [List.ofFn_succ, Fin.cases_zero, Fin.cases_succ] using
    affineMomentPolynomial_hasSum b c B D hB a d e F hdegree (φ Y)
      (fun v => profileCoefficient P Y (List.ofFn v) K) (hactual Y hY)
      M W (w Y) (hm Y hY) (hw Y hY)
end WP.HigherOrder.JointBoundary
