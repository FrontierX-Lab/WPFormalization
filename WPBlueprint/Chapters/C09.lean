import WPFormalization.Statements
import WPBlueprint.Chapters.C08
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "10-sharp-extraction" =>

# Extraction with an inverse-genus error

The local limit theorem 9.7 has no rate. Its quantitative form, Proposition {bpref "prop:quantitative-local"}[D.1] in Appendix D, gives only a power rate in $`\min(h,\mu)`, and its Gaussian approximation degenerates when the coefficient index stays bounded. To obtain an error of order $`g^{-1}` uniformly in the index, we retain an exact Poisson factor rather than its Gaussian approximation. Theorem {bpref "thm:sharp-extraction"}[10.1] supplies the estimate used for the leading absolute-volume formula in Section 11, and Theorem {bpref "thm:canonical-expansion"}[10.2] extends it to all orders. Both theorems are proved in Appendix D.

Why a Poisson factor. Near zero cusp weight the leading term of $`\Phi_g^{(p)}` behaves like $`\mathrm e^{hS(x)}` with $`S(x)=2x+O(x^2)`; see {bpref "eq:CE1"}[10.1] below. At a positive weight $`x`, the normalized terms $`\mathrm e^{-2hx}(2hx)^k/k!` are exactly Poisson probabilities with mean $`2hx`. Hence, when the coefficient index $`k` stays bounded, the cusp count under the saddle weight is approximately Poisson, and a Gaussian approximation of its point mass makes a relative error of order $`1/k`, which does not tend to zero. If the leading term is written instead with the exact Poisson mass $`\mathfrak p_k=\mathrm e^{-k}k^k/k!` at the mean, the ratio of the true coefficient to this model is $`1+O(1/h)` for every $`k`. For large $`k` one has $`\sqrt{2\pi k}\,\mathfrak p_k\to1`, and the Gaussian formula is recovered.

Fix $`p\ge1`, put $`F_h=\Phi_g^{(p)}`, $`h=2g-2+p`, and write

:::definition "eq:CE1" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:PF3")
%%%
source := { document := "paper-v3", spans := #[{ page := "46", anchor := "eq:CE1", citation := "Equation 10.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 10.1 — Extraction action and amplitude.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathcal J_{g,p}(x)=\mathcal J_{g,p}(0)\mathrm{e}^{hS(x)}B_p(x),\qquad
 S=\log\frac{\mathcal Z(0)}{\mathcal Z(Y(x))},\qquad
 B_p=\frac{r^{p/2}\sqrt{A\Theta}}{r(0)^{p/2}\sqrt{A(0)\Theta(0)}}.`


:::



We view $`\mathcal J` as a function of $`x=X(Y)`. Then $`\mathscr DS=\Psi` and $`\mathscr D\log B_p=\beta_p\Psi`. For each integer $`k\ge1`, choose $`x` by $`h\Psi(x)=k`, and put $`v=\mathscr D\Psi`, $`\sigma^2=hv`, $`M=\min(h,k)`. Let $`\mathfrak p_k=\mathrm{e}^{-k}k^k/k!`, with $`\mathfrak p_0=1`.

:::theorem "thm:sharp-extraction" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:CG1")
%%%
source := { document := "paper-v3", spans := #[{ page := "47", anchor := "thm:sharp-extraction", citation := "Theorem 10.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Theorem 10.1 — Uniform Poisson-corrected extraction.

For fixed $`p\ge1`, uniformly over integers $`k\ge0`, 

$$`[z^k]F_h(z)=\frac{\mathcal J_{g,p}(x)}\pi x^{-k}\mathfrak p_k
       \sqrt{\frac{k}{h\mathscr D\Psi(x)}}\,(1+O_p(h^{-1})).`

 At $`k=0` take $`x=0` and interpret both $`k`-dependent factors by continuity as one.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



The proof, given in Subsections D.2–D.4, has three parts: transfer a sufficiently long marked expansion, namely Theorem {bpref "thm:full-expansion"}[8.2] at a fixed finite order, to small complex neighborhoods of the real saddle point; identify the Poisson correction; and estimate the small indices directly. The argument uses no estimate for a growing number of markings and never differentiates a remainder; away from zero, the model is continued analytically only to small neighborhoods of the real axis.

## The full expansion at a prescribed cusp count

Theorem {bpref "thm:sharp-extraction"}[10.1] recovers the leading term with an inverse-genus error. We now extract the whole marked expansion, keeping the remainder uniform in both the cusp count and the truncation order. The result is Theorem {bpref "thm:canonical-expansion"}[10.2], which provides the remaining input for the full absolute-volume expansion in Section 11.

The idea. Away from zero cusp weight, including near the critical point, the coefficient integral has a nondegenerate saddle point, and the Gaussian method of steepest descent gives an expansion in $`1/h`. Near zero this fails for bounded $`k`: the saddle point of $`\mathrm e^{hS(z)}z^{-k}` approaches the singularity of $`z^{-k}` at the origin. Following Temme, we change variables so that the phase $`S(z)-(k/h)\log z` becomes exactly $`u-(k/h)\log u`. The coefficient is then a Poisson coefficient $`[u^k]\mathrm e^{hu}f(u)` with an analytic amplitude $`f`. Expanding $`f` about $`u=k/h` produces the signed central polynomials $`T_m(k)` of the coefficient operator in D.19, divided by powers of $`h`. These are not the central moments of a probability distribution: for example, $`T_2(k)=-k`. The resulting expansion in $`1/h` is uniform in $`k`, including $`k=0`. The two expansions are identified on an overlap of their ranges.

The proof, given in Subsections D.5–D.7, uses a Poisson integral near zero cusp weight and a Gaussian integral away from zero, including near criticality. A change of phase identifies the two coefficient formulas on their overlap. Near zero we follow Temme’s method for uniform Laplace and loop integrals \[80\] Sections 2.3 and 3.7.

Retain $`h=2g-2+p`, $`k=h\Psi(x)`, $`v=\mathscr D\Psi(x)` and the functions $`S,B_p` in {bpref "eq:CE1"}[10.1]. Regard $`\mathcal L_{p,j}` as functions of $`x` via $`Y(x)`. Write

:::definition "eq:CG1" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:CE1")
%%%
source := { document := "paper-v3", spans := #[{ page := "47", anchor := "eq:CG1", citation := "Equation 10.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 10.3 — Poisson corrected normalization.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathcal Q_{g,p,k}=
 \frac{\mathcal J_{g,p}(x)}\pi x^{-k}\mathfrak p_k
                   \sqrt{\frac{k}{hv}}.`


:::



The conventions at $`k=0` are those of Theorem {bpref "thm:sharp-extraction"}[10.1].

Put $`\mathcal L_{p,0}=1`. Let $`\mathfrak G_w` be the linear functional on polynomials which maps $`w^{2a}` to $`(-1)^a(2a-1)!!` and odd powers to zero. Define the formal even series 

$$`\begin{aligned}
 \mathcal N_p(\tau,x)=\mathfrak G_w\Bigg[
 &\exp\!\left\{
 \sum_{m\ge3}\frac{\tau^{m-2}\mathscr D^mS}{m!v^{m/2}}w^m
 +\sum_{m\ge1}\frac{\tau^m\mathscr D^m\log B_p}{m!v^{m/2}}w^m
 \right\}\\[-2pt]
 &\hspace{20pt}\cdot\sum_{s\ge0}\tau^{2s}
       \mathcal L_{p,s}(x\mathrm{e}^{\tau w/\sqrt v})\Bigg].
\end{aligned}`

 Formal composition in the last line means Taylor expansion at $`x`. At every order only finitely many derivatives are used. If $`\sqrt{2\pi k}\,\mathfrak p_k\sim\sum_{j\ge0}s_jk^{-j}`, $`s_0=1`, set

:::definition "eq:CG3" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:CE1")
%%%
source := { document := "paper-v3", spans := #[{ page := "48", anchor := "eq:CG3", citation := "Equation 10.5", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 10.5 — Extracted correction coefficients.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathcal A_{p,j}(Y)=[\tau^{2j}]
       \frac{\mathcal N_p(\tau,X(Y))}
            {\displaystyle\sum_{i\ge0}s_i\Psi(X(Y))^{-i}\tau^{2i}}.`


:::



This initially defines the functions for $`0<Y<y_0`.

:::theorem "thm:canonical-expansion" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:CG1, eq:CG3")
%%%
source := { document := "paper-v3", spans := #[{ page := "48", anchor := "thm:canonical-expansion", citation := "Theorem 10.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Theorem 10.2 — Uniform expansion at a prescribed cusp count.

For every fixed $`p\ge1` there are constants $`C_p,\mathfrak B_p,c_p,h_p>0` such that, for $`h=2g-2+p\ge h_p`, every integer $`k\ge0` and $`0\le K\le c_p\sqrt h`, 

$$`\left|\frac{[z^k]\Phi_g^{(p)}}{\mathcal Q_{g,p,k}}
       -\sum_{j=0}^K\frac{\mathcal A_{p,j}(Y)}{h^j}\right|
 \le\frac{C_p\mathfrak B_p^{K+1}((K+1)!)^2}{h^{K+1}},
 \qquad h\Psi(X(Y))=k,`

 where $`\mathcal A_{p,0}=1`. The coefficients are analytic on one complex neighborhood $`\Omega_p` of $`[0,y_0]`, with $`\|\mathcal A_{p,j}\|_{\Omega_p}\le C_p\mathfrak B_p^j(j!)^2`, and $`\mathcal A_{p,j}(0)=\mathcal L_{p,j}(0)`. For a sufficiently small fixed $`c'_p>0`, truncation at $`K=\lfloor c'_p\sqrt h\rfloor` has relative error $`O_p(\mathrm{e}^{-a_p\sqrt h})`, uniformly in $`k`, for some $`a_p>0`. The marking count is fixed. The infinite series need not converge.
:::



The first coefficient $`\mathcal A_{p,1}` is given explicitly in {bpref "eq:CG12"}[D.24], and its value at the critical endpoint in {bpref "eq:CG13"}[D.25]. Retaining it improves the relative remainder to $`O_p(h^{-2})` over every coefficient index.
