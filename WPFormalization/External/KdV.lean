import WPFormalization.Statements.IntersectionInterface

/-! The classical first integrated KdV equation for ordinary descendant numbers.

Primary source: K. Liu, M. Mulase, H. Xu, "Recursions and asymptotics of
intersection numbers", PDF p.3, Eq.(6):
https://www.math.ucdavis.edu/~mulase/texfiles/RecursionAsymp.pdf
The same page Eq.(3) states the equivalence of the weighted DVV recursion with
the Witten--Kontsevich theorem. The transfer to an arbitrary PsiTheory uses
uniqueness of the classical DVV/Virasoro theory with the two specified bases;
see also Itzykson--Zuber, hep-th/9201001, PDF p.32, Theorem2 / Eq.(4.12).
This standard uniqueness/identification is included in the deferred classical
proof, along with the ordinary unstable and wrong-dimension zero conventions.

Only the unshifted descendant identity is admitted. There is no parameter Y,
background time, kernel, normalization, profile, or paper-specific estimate in
this interface. The shifted finite-background transformation is proved locally.
-/
noncomputable section
namespace WP.External

/- Eq.(6), with ordered splitting of the entire labelled descendant tail. -/
@[blueprint "ext:kdv"]
theorem integrated_first_kdv (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g)
    (L : List ℤ) (hL : ∀ k ∈ L, 0 ≤ k) :
    (2*(g : ℝ)+(L.length : ℝ)-1)*P.psi g (0 :: L) =
      P.psi (g-1) (List.replicate 4 0 ++ L)/12 +
      (1/2 : ℝ)*∑ j ∈ Finset.range (g+1),
        ∑ I ∈ (Finset.range L.length).powerset,
          P.psi j (List.replicate 2 0 ++ selected L I)*
            P.psi (g-j) (List.replicate 2 0 ++ selected L ((Finset.range L.length) \ I)) := by
  sorry

/- The tau_1 tau_0 form follows from the existing classical dilaton law. -/
@[blueprint "ext:kdv"]
theorem first_kdv_descendants (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g)
    (L : List ℤ) (hL : ∀ k ∈ L, 0 ≤ k) :
    P.psi g (1 :: 0 :: L) =
      P.psi (g-1) (List.replicate 4 0 ++ L)/12 +
      (1/2 : ℝ)*∑ j ∈ Finset.range (g+1),
        ∑ I ∈ (Finset.range L.length).powerset,
          P.psi j (List.replicate 2 0 ++ selected L I)*
            P.psi (g-j) (List.replicate 2 0 ++ selected L ((Finset.range L.length) \ I)) := by
  have hs : Stable g (0 :: L).length := by unfold Stable; simp only [List.length_cons]; omega
  calc
    _ = (2*(g : ℝ)-2+(0 :: L).length)*P.psi g (0 :: L) := P.dilaton g _ hs
    _ = (2*(g : ℝ)+(L.length : ℝ)-1)*P.psi g (0 :: L) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    _ = _ := integrated_first_kdv P g hg L hL

end WP.External
