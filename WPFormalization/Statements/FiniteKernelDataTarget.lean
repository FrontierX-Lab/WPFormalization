import WPFormalization.HigherOrder.FiniteDataEnvironment
import WPFormalization.HigherOrder.Triangular

/-! The previously proposed own C.3 finite-data goals, now fixed as specifications.
The data index and values are the actual ones in FiniteDataEnvironment.
Neither definition supplies a producer; every step of the common induction
must still be instantiated before either goal can be counted as proved. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData

def PolynomialDependenceTarget (P:PsiTheory):Prop :=
  ∀p J:ℕ,1≤p → ∃N:ℕ,
    ∃e:ℕ→List ℕ→MvPolynomial (Index J N) ℝ,
    ∃c g:ℕ→MvPolynomial (Index J N) ℝ,
      ∀Y∈Set.Icc (0:ℝ) y₀,∀k≤J,
        (∀d:List ℕ,d.length=p → profileCoefficient P Y d k=
          MvPolynomial.eval (value J N Y) (e k d)) ∧
        cuspCoefficient P Y p k=MvPolynomial.eval (value J N Y) (c k) ∧
        genusCoefficient P Y p k=MvPolynomial.eval (value J N Y) (g k)

def stratum (p b:ℕ)(d:Fin p→ℕ):Fin p→Option (Fin (b+1)) := fun i=>
  if hi:d i≤b then some ⟨d i,by omega⟩ else none

/-- The actual polynomial-stratum statement needed to reduce the kernel sums.
It remains an own goal: neither its existence nor the displayed degree bound
is included among the inputs of the canonical hierarchy. -/
def ProfileBoundaryPolynomialTarget (P:PsiTheory):Prop :=
  ∀p J:ℕ,1≤p →
    ∃F:ℝ→(Fin p→Option (Fin (boundaryCutoff J+1)))→MvPolynomial (Fin p) ℝ,
      (∀Y∈Set.Icc (0:ℝ) y₀,∀σ,(F Y σ).totalDegree≤2*J) ∧
      ∀Y∈Set.Icc (0:ℝ) y₀,∀d:Fin p→ℕ,
        profileCoefficient P Y (List.ofFn d) J=
          MvPolynomial.eval (fun i=>(d i:ℝ)) (F Y (stratum p (boundaryCutoff J) d))

end WP.HigherOrder.KernelFiniteData
