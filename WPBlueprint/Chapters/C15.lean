import WPFormalization.Statements
import WPBlueprint.Chapters.C14
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "15-conclusion" =>

# Concluding remarks and open questions

The results above show that one real parameter, determined by the cusp density, governs the large-genus behavior of $`V_{g,n}` in every regime. As $`n/g` runs from zero to infinity, the saddle $`X(Y_{n/g})` moves from the fixed-cusp regime of Mirzakhani and Zograf to the Bessel singularity $`x_c` of the fixed-genus theory of Manin and Zograf. The volume ratios, the boundary factor $`\mathfrak b_Y`, the short-curve intensities $`w_k` and the tight-length scale $`\alpha` interpolate in the same way.

The coefficients of the normalized volume expansion are analytic in $`Y` on a neighborhood of the compact interval $`[0,y_0]`. This is the precise sense in which the two endpoint regimes fit into one expansion. It avoids the loss of uniformity of the fixed-$`n` expansion at $`n\asymp\sqrt g`, while retaining an error bound independent of $`n`.

The short geometry nevertheless changes at the scale $`\sqrt g`. For $`n=o(\sqrt g)`, Shen and Wu proved a uniform spectral gap \[79\] Theorem 3. At $`n/\sqrt g\to c\in(0,\infty)`, the primitive length spectrum is a Poisson background together with independent clusters formed by two-cusp pairs of pants (Theorem {bpref "thm:critical-cluster"}[14.6]). Above this scale, short curves bounding genus-zero subsurfaces containing cusps have the statistics of Theorem {bpref "thm:pants-poisson"}[14.1], and the spectral gap closes (Corollary {bpref "cor:spectral"}[1.6]).

The proof rests on three features that may be useful beyond Weil–Petersson volumes. Along the string flow, the alternating $`\kappa_1`–$`\psi` formula becomes a recursion with nonnegative coefficients, so that comparison and monotonicity arguments hold uniformly in the deformation parameter. The deformation ends at pure $`\psi` intersection numbers, where Painlevé I fixes the integration constants without any resurgence assumption. Finally, the positive convolution factor of Lemma {bpref "lem:convolution"}[9.1] turns estimates for generating functions into a local limit theorem that holds uniformly from bounded cusp counts up to the critical cusp weight. The geometric consequences combine these volume estimates with the integration formulas and short-curve arguments credited in Section 14.

## Cusp weights and the JT spectral edge

:::lemma_ "eq:jt-string-normalization" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "def:bessel, eq:H8")
%%%
source := { document := "paper-v3", spans := #[{ page := "65", anchor := "subsec:jt-edge", citation := "Section 15.1 string substitution and defect generating-function normalization", pdf := some { path := "source/paper.pdf" } }] }
%%%

R35 implementation: the complete mathematical deduction has a Lean producer linked below. The physical interpretation cited here is background; the local identities and remainder estimates are proved from the defined mathematical functions, without a new physical-model assumption.

Saad, Shenker and Stanford related the genus expansion of Jackiw–Teitelboim (JT) gravity to a matrix integral, with Weil–Petersson volumes as its geometric input \[77\]. The parameter $`Y` describes a spectral edge in its defect deformation, introduced by Maxfield–Turiaci and by Witten \[59\]; \[82\]. We record the normalization to relate the uniform estimates to that model. A defect of opening angle $`2\pi\alpha` is a cusp at $`\alpha=0` \[22\] Section 2. Let $`\lambda_{\mathrm{def}}` be its weight, distinct from the cusp density $`\lambda=n/g`, and use the convention $`2\gamma=1` of Maxfield–Turiaci \[59\]. Their string equation at $`\alpha=0` and its branch connected to the undeformed edge are 

$$`\frac{\sqrt{E_0}}{2\pi}I_1(2\pi\sqrt{E_0})
       +\lambda_{\mathrm{def}}=0,\qquad
 E_0=-\frac{Y}{\pi^2},\qquad x=2\pi^2\lambda_{\mathrm{def}}.`

 The Bessel expressions are interpreted by their entire power series. Substitution gives exactly $`X(Y)=x`. Moreover, the definition {bpref "eq:H8"}[4.7] gives, for $`g\ge2`, 

$$`\sum_{n\ge0}V_{g,n}\frac{\lambda_{\mathrm{def}}^n}{n!}
       =(2\pi^2)^{3g-3}\Phi_g(x).`

 Thus a fixed cusp count is a coefficient of the defect-weighted amplitude, whereas $`Y` parametrizes its spectral edge.

:::

:::lemma_ "eq:jt-abel-critical-edge" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:P1, eq:P10")
%%%
source := { document := "paper-v3", spans := #[{ page := "65", anchor := "subsec:jt-edge", citation := "Section 15.1 Abel-to-kernel equality and cubic critical density", pdf := some { path := "source/paper.pdf" } }, { page := "66", anchor := "subsec:jt-edge", citation := "Section 15.1 Abel-to-kernel equality and cubic critical density", pdf := some { path := "source/paper.pdf" } }] }
%%%

R35 implementation: the complete mathematical deduction has a Lean producer linked below. The physical interpretation cited here is background; the local identities and remainder estimates are proved from the defined mathematical functions, without a new physical-model assumption.

The genus-zero density, with its overall topological factor removed, can be written using our kernel. Specializing the Abel integral in \[59\] equation (3.50) to $`\alpha=0` gives 

$$`\rho_0(E)=\frac1{4\pi}\int_{E_0}^{E}
        \frac{I_0(2\pi\sqrt u)}{\sqrt{E-u}}\,\mathrm du
   =\frac{\sqrt q}{2\pi}K_Y(-2\pi^2q),\qquad q=E-E_0\ge0.`

 For the second equality set $`u=E_0+q(1-s^2)` and use {bpref "eq:P1"}[2.1]. At $`Y=0` this is the JT density $`\sinh(2\pi\sqrt E)/(4\pi^2)`. At $`Y=y_0`, put $`b=-X''(y_0)>0`. Since $`a(y_0)=0`, expansion of $`K_{y_0}` gives 

$$`\rho_0(E_0+q)=\frac{\pi b}{3}q^{3/2}+O(q^{5/2}).`

 The square-root edge has become a cubic critical edge, the local geometry associated with the $`(2,3)` critical point. This identifies the physical meaning of the same endpoint at which the normalized intersection recursion reduces to pure $`\psi` intersections.

:::

:::lemma_ "eq:jt-critical-action" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP2, lem:parameter, eq:PF1")
%%%
source := { document := "paper-v3", spans := #[{ page := "66", anchor := "subsec:jt-edge", citation := "Section 15.1 critical action in delta and spectral-gap coordinates", pdf := some { path := "source/paper.pdf" } }] }
%%%

R35 implementation: the complete mathematical deduction has a Lean producer linked below. The physical interpretation cited here is background; the local identities and remainder estimates are proved from the defined mathematical functions, without a new physical-model assumption.

The exponent in the large-genus action agrees with this critical geometry. With $`\delta=y_0-Y`, the endpoint expansions of Section 3 give 

$$`x_c-x=\frac b2\delta^2(1+O(\delta)),\qquad
 \mathcal Z=\frac{2\sqrt3\,b}{5}\delta^{5/2}(1+O(\delta))
       =\frac{2^{9/4}\sqrt3}{5b^{1/4}}
          (x_c-x)^{5/4}\bigl(1+O(\sqrt{x_c-x})\bigr).`

 The marked expansion in Theorem {bpref "thm:full-expansion"}[8.2] uses the full action $`\mathcal Z(Y)` and remains uniform as $`Y` approaches $`y_0`. Replacing the action by its leading critical power would instead introduce a multiplicative factor $`\exp(O(g\sqrt{x_c-x}))` for fixed marking count. That replacement is not uniform in an arbitrary joint limit. In formal genus counting, the corresponding balance is between the string coupling $`\hbar` and $`(x_c-x)^{5/4}`; the genus index $`g` is not the inverse string coupling. A double-scaled sum over all genera requires a separate summation prescription and estimates beyond the large-genus coefficient asymptotics proved here.

:::

## Open questions

We conclude with some questions that the present methods leave open.

Actual Gevrey-1 remainders. The most direct analytic strengthening would replace the squared factorial in Theorem {bpref "thm:intro-absolute"}[1.1] by a single factorial, with constants uniform in the cusp count and truncation order $`K\le cg`. A sufficiently small linear truncation would then give error $`O(\mathrm e^{-ag})`. The pure-$`\psi` endpoint already has this order of remainder (Subsection C.9), but transporting it across the whole parameter interval requires sharper estimates for the actual recursion. In the present proof the squared factorial comes from the degree paths in the profile recursion (Subsection 8.2); bounds on the formal coefficients alone would not settle the question, since the actual remainders must be controlled as well.

Rate for adjacent ratios. Theorem {bpref "thm:coefficient"}[1.4] has the uniform error $`O(g^{-1/8})`, and $`O_\varepsilon(g^{-1/4})` for $`k\ge\varepsilon g`; neither exponent is claimed to be optimal (Appendix E). What is the optimal uniform rate?

Other backgrounds. The derivation of the recursion {bpref "eq:H9"}[4.8] uses only the string, dilaton and Dijkgraaf–Verlinde–Verlinde equations, and applies to other backgrounds of Kontsevich–Witten times; the higher Weil–Petersson volumes of Kaufmann, Manin and Zagier arise in this way \[48\]; \[58\]. For which backgrounds does the deformed recursion have nonnegative coefficients, and does the uniform analysis of this paper then extend?

Several boundary components. Can one obtain relative asymptotics for mixed intersection numbers when both the number of nonzero degrees and their sum grow with the genus, uniformly over their allocation among the markings? Proposition {bpref "prop:bounded-boundaries"}[9.4] treats a fixed number of bounded nonzero lengths; it does not provide this control of individual mixed intersections.

Geometry and spectrum. Theorem {bpref "thm:tight-spectrum"}[14.4] determines the tight spectrum at every cusp density, while Theorem {bpref "thm:critical-cluster"}[14.6] identifies the pants clusters in the ordinary spectrum when $`n/\sqrt g` has a positive finite limit. What is the joint distribution of ordinary geodesics in the same homotopy class after filling the cusps, when $`n` is proportional to $`g`? Our spectral results are upper bounds for small eigenvalues; their limiting distribution would require additional geometric input.
