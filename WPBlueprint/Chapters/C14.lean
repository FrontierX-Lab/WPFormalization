import WPFormalization.Statements
import WPBlueprint.Chapters.C13
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "14-geometry" =>

# Short curves and small eigenvalues

The analytic estimates enter geometry through ratios of volumes of cut surfaces, by Mirzakhani’s integration formula \[61\]. We first apply the adjacent-volume limit to Shen–Wu’s vanishing-gap argument \[79\] (Subsection 14.1). We then determine the short-curve process and the systole above the scale $`\sqrt g` (Subsection 14.2) and deduce many small eigenvalues (Subsection 14.3). The last two subsections state the limit of the tight length spectrum at every cusp density and of the full primitive spectrum at the critical scale $`n\asymp\sqrt g`; their proofs are given in Appendices F and G. The critical result uses volume bounds of Mirzakhani–Zograf and Shen–Wu and only the zero-density case of the volume-ratio limits, not the uniform expansion.

## The first positive eigenvalue

The simplest spectral consequence uses only the discrete cusp ratio $`D_{g,n-1}`. A short curve enclosing two cusps bounds a pair of pants of fixed area $`2\pi`, joined to the rest of the surface through a short boundary. This gives a small Cheeger ratio and hence a small Rayleigh quotient. Shen–Wu’s second-moment argument makes such a curve probable. Shen and Wu asked for the adjacent-volume limit needed to extend this argument beyond $`n=o(g)` \[79\] Question 3. Theorem {bpref "thm:volume"}[1.3] provides that limit along every sequence with $`g\to\infty`.

:::proof "cor:spectral" (uses := "thm:volume, ext:shen-wu")
Put $`n=n(g)` and 

$$`L_g=\left(\frac{\sqrt g}{n}\right)^{1/2}.`

 Let $`N_g(X)` count the simple closed geodesics of length at most $`L_g` whose complement has components of topological types $`(0,3)` and $`(g,n-1)`. Proposition 35 of \[79\], in the notation of its arXiv version 4, states under the sole assumption $`n/\sqrt g\to\infty` that 

$$`\liminf_{g\to\infty}\mathbb P^{\mathrm{WP}}_{g,n}\{N_g\ge1\}
 \ge \liminf_{g\to\infty}
 \frac{V_{g,n-1}^{2}}{V_{g,n}V_{g,n-2}}.`

 The ratio on the right is $`D_{g,n-1}`, which tends to one by Theorem {bpref "thm:volume"}[1.3]. Thus $`\mathbb P^{\mathrm{WP}}_{g,n}\{N_g\ge1\}\to1`. The same conclusion also follows within this paper: $`N_g` is the count $`N_{L_g}` of Subsection 14.2, with $`q_g` as in {bpref "eq:PS1"}[14.1], and since $`L_g\to0` and $`q_gL_g^2\asymp n\sqrt g/(g+n)\to\infty`, Proposition {bpref "prop:pants-concentration"}[14.2] gives $`N_g/(q_gL_g^2)\to1` in probability. Its proof is the same second-moment argument, with $`D_{g,n-1}\to1` as the volume input.

Write $`\mathfrak h(X)` for the Cheeger constant. On the event $`N_g\ge1`, a counted geodesic bounds a hyperbolic pair of pants of area $`2\pi`; the other component has area $`2\pi(2g+n-3)\ge2\pi` for all sufficiently large $`g`. This separating curve is an admissible Cheeger cut, so 

$$`\mathfrak h(X)\le \frac{L_g}{2\pi}.`

 Let $`\mathcal R(X)` be the infimum of the Rayleigh quotient over nonzero $`H^1(X)` functions orthogonal to constants. Buser’s inequality \[15\] Theorem 7.1, in the form recorded in \[79\] Theorem 11 for complete noncompact hyperbolic surfaces, gives $`\mathcal R(X)\le c\mathfrak h(X)` with an absolute constant $`c`. Since $`L_g\to0`, this upper bound is eventually smaller than both $`\varepsilon` and $`1/4`. The essential spectrum starts at $`1/4`; the min–max principle, as recalled in \[79\] Theorem 7, therefore yields a positive discrete eigenvalue $`\lambda_1(X)=\mathcal R(X)<\varepsilon` on $`N_g\ge1`, for all sufficiently large $`g`. This proves the asserted probability limit.
:::



The use of $`D_{g,n-1}` above is the only change to the final step of Shen–Wu’s proof: under their condition $`n=o(g)` this limit follows from \[66\] Lemma 5.1, as they note. The short-curve estimate, the Cheeger cut, and the passage to a discrete eigenvalue are their geometric and spectral inputs.

## Short-curve processes and the systole

We now determine the limiting process of short curves and the systole. The moment estimates proved here will also be used in Subsection 14.3 to count many disjoint short pairs of pants. Throughout this and the next subsection, $`g\to\infty`, $`n/\sqrt g\to\infty`, and $`X` has law $`\mathbb P^{\mathrm{WP}}_{g,n}`. Let $`\mathcal P_2(X)` be the set of unoriented simple closed geodesics bounding a pair of pants with two cusps. Define the deterministic intensity parameter

:::definition "eq:PS1" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:SP3")
%%%
source := { document := "paper-v3", spans := #[{ page := "57", anchor := "eq:PS1", citation := "Equation 14.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 14.1 — Short-pants length scale.

In the setup and notation of this section, the paper defines or asserts:



$$`q_g=\frac{n(n-1)}{8g\mathcal C(n/g)}.`


:::



The profile endpoints in Theorem {bpref "thm:volume"}[1.3] imply $`q_g\asymp n^2/(g+n)\to\infty`. In particular $`q_g\sim n^2/(32\pi^2g)` when $`n/g\to0`, and $`q_g\sim x_cn/(8\pi^2)` when $`n/g\to\infty`.

We write $`\operatorname{PPP}(\nu)` for a Poisson point process with intensity measure $`\nu`.

:::theorem "thm:pants-poisson" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP3, eq:PS1")
%%%
source := { document := "paper-v3", spans := #[{ page := "58", anchor := "thm:pants-poisson", citation := "Theorem 14.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Theorem 14.1 — Short-curve processes and the systole.

Scope from Section 14.2: integer cusp counts, genus tending to infinity, and $`n/\sqrt g\to\infty`. All further hypotheses in the statement apply as written.

(i) Curves cutting off two cusps. The random locally finite counting measures 

$$`\sum_{\gamma\in\mathcal P_2(X)}
       \delta_{\sqrt{q_g}\ell_\gamma}
 \ \Longrightarrow\ \operatorname{PPP}(2t\,\mathrm{d}t)
 \quad\hbox{on }[0,\infty)`

 converge in distribution for the vague topology. Thus counts in finitely many disjoint bounded intervals $`[a_i,b_i]` converge jointly to independent Poisson variables with means $`b_i^2-a_i^2`. If $`\ell_{\min}^{(2)}` is the shortest length in $`\mathcal P_2(X)`, with value infinity when this set is empty, then 

$$`\mathbb P^{\mathrm{WP}}_{g,n}
 \{\sqrt{q_g}\ell_{\min}^{(2)}>t\}\longrightarrow \mathrm{e}^{-t^2}
 \qquad(t\ge0).`

 (ii) All planar cusp types. Let $`\mathcal P_k(X)` consist of simple geodesics whose genus-zero side contains exactly $`k` cusps. If $`n/g\to\lambda\in[0,\infty]`, put $`x_\lambda=X(Y_\lambda)`, where $`\lambda(Y_\lambda)=\lambda`, with $`x_0=0` and $`x_\infty=x_c`. Define 

$$`w_k(x)=\frac{2V_{0,k+1}}{k!}
             \left(\frac{x}{2\pi^2}\right)^{k-2},\qquad
 W(x)=\sum_{k\ge2}w_k(x)=\frac{2\Phi_0'(x)}{x^2}.`

 Here $`w_2(0)=W(0)=1`, $`w_k(0)=0` for $`k>2`, and $`W(x_c)<\infty`. Then 

$$`\sum_{k\ge2}\ \sum_{\gamma\in\mathcal P_k(X)}
       \delta_{(\sqrt{q_g}\ell_\gamma,k)}
 \ \Longrightarrow\
 \operatorname{PPP}\!\left(2t\,\mathrm{d}t\otimes
                    \sum_{k\ge2}w_k(x_\lambda)\delta_k\right).`

 Convergence is for the vague topology on the product with the discrete type space. The projection to lengths also converges, to $`\operatorname{PPP}(2W(x_\lambda)t\,\mathrm{d}t)`.

(iii) Primitive geodesics and the systole. This is also the limit of the process of all unoriented primitive closed geodesics, at the same rescaling. Writing $`\operatorname{sys}(X)` for the shortest closed geodesic length, we have 

$$`\mathbb P^{\mathrm{WP}}_{g,n}
 \{\sqrt{q_g}\operatorname{sys}(X)>t\}
 \longrightarrow \mathrm{e}^{-W(x_\lambda)t^2}\qquad(t\ge0).`

 With probability tending to one every systolic curve is planar separating. Select one by any measurable tie rule, and let $`K_g` be its planar-side cusp count, with value zero if it is not planar. Then $`\bigl(\sqrt{q_g}\operatorname{sys}(X),K_g\bigr)` converges jointly to a pair $`(Z,K)` with 

$$`\begin{aligned}
 \mathbb P\{Z\in \mathrm{d}t,K=k\}
 &=2t\,w_k(x_\lambda)\mathrm{e}^{-W(x_\lambda)t^2}\,\mathrm{d}t,\\
 \mathbb P\{K=k\}&=\frac{w_k(x_\lambda)}{W(x_\lambda)}
 \qquad(t>0,\ k\ge2).
 \end{aligned}`


:::



The method of factorial moments for curves separating off a prescribed number of cusps has a direct precedent in Hide–Thomas \[41\] Theorem 1.7 for punctured spheres, which also treats summed types and nested configurations \[41\] Remark 1.9 and Proposition 3.6. Here the uniform volume ratios give the entire family of type intensities for diverging genus at every cusp density above the square-root scale. These planar curves become contractible after the cusps are filled; they are excluded from the tight spectrum of \[13\] Definition 2.1. The all-primitive process of Mirzakhani–Petri \[65\] Theorem 4.1 concerns closed surfaces at fixed physical lengths. Here the full process is observed on a shrinking scale; a tight-spectrum limit at its longer natural scale is a separate question.

Factorial moments. For sufficiently small $`L`, the collar lemma forces all curves counted by $`N_L=\#\{\gamma\in\mathcal P_2(X):\ell_\gamma\le L\}` to be disjoint. Their pants interiors are also disjoint. Otherwise one pants boundary would be an interior essential geodesic of the other pants, hence boundary-parallel, contradicting uniqueness of geodesic representatives. Thus their pairs of cusp labels are disjoint, and their complement has type $`(g,n-r)` for $`r` pants. We have $`g\ge2` eventually, so the exceptional double-pants decomposition of a four-punctured sphere does not arise.

Mirzakhani’s integration formula \[61\]; \[64\], with the same conventions as \[79\] Lemma 29, gives, for any fixed $`r` and short length windows $`I_1,\ldots,I_r`, the ordered distinct-curve integral

:::proposition "eq:PS3" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP3")
%%%
source := { document := "paper-v3", spans := #[{ page := "59", anchor := "eq:PS3", citation := "Equation 14.6", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 14.6 — Ordered pants factorial moments.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathbb E\!\sum_{\substack{\gamma_1,\ldots,\gamma_r\in\mathcal P_2(X)\\
                            \text{distinct}}}
       \prod_{j=1}^r\mathbf1_{\ell_{\gamma_j}\in I_j}
 =\frac{(n)_{2r}}{2^r V_{g,n}}
    \int_{I_1\times\cdots\times I_r}
       V_{g,n-r}(x_1,\ldots,x_r,0^{n-2r})
       \prod_{j=1}^r x_j\,\mathrm{d}x_j.`


:::



Here $`(n)_{2r}=n(n-1)\cdots(n-2r+1)`. The factor $`2^{-r}` removes the order of the two labels within each pair. The tuple of curves is ordered, so there is no $`r!` divisor. Each pants volume is $`V_{0,3}=1`. Mirzakhani’s boundary estimate \[64\] Lemma 3.2, in the form of \[79\] Lemma 14, 

$$`1\le\frac{V_{g,m}(\mathbf x)}{V_{g,m}}
       \le\exp\!\left(\frac12\sum_jx_j\right)`

 is uniform in the topological type. For fixed $`r`, it replaces the boundary volume in {bpref "eq:PS3"}[14.6] by $`V_{g,n-r}(1+O_r(L))` when all $`I_j\subset[0,L]`.

Theorem {bpref "thm:volume"}[1.3] also implies, for every fixed $`r`, 

$$`\frac{V_{g,n-r}}{V_{g,n}}
  =(2g\mathcal C(n/g))^{-r}(1+o(1)).`

 Indeed this is a product of $`r` adjacent cusp ratios. Replacing $`(n-j)/g` by $`n/g` changes their profile by $`1+O_r(n^{-1})`, because $`\lambda\partial_\lambda\log\mathcal C(\lambda)` is bounded: this follows from analyticity in the interior and the two endpoint expansions.

:::proof "thm:pants-poisson" (uses := "thm:volume, prop:bounded-boundaries, lem:point-mass, eq:PS3, ext:collar, ext:mir-integration")
We prove the planar process by bounding the tail over cusp types and computing the mixed factorial moments for any fixed collection of types. We then exclude the other topological types on the same length scale; this identifies the full primitive process and the systole. Write $`P=2\pi^2`, $`h=2g-1`, $`m=n-1`, and $`F_h=\Phi_g'`. Choose $`x\in(0,x_c)` by $`h\Psi(x)=m` and put $`q_g^*=nx/(4P)`. The effective density is $`2(n-1)/(2g-1)`. The boundedness of $`\lambda\partial_\lambda\log X(Y_\lambda)`, including its endpoint limits, implies $`q_g^*/q_g\to1` and $`q_g^*\to\infty`.

Step 1: a uniform tail bound over cusp types. We first show that curves cutting off a large number of cusps contribute negligibly, uniformly along the sequence. The input is the coefficient-ratio bound 14.9, which compares volumes whose cusp counts differ by $`j`. By the positive convolution 9.1 and Lemma {bpref "lem:point-mass"}[9.3], every point mass is at most $`C/\sigma`, where $`\sigma^2=h\mathscr D\Psi(x)`. The local limit 9.7 gives a lower bound $`c/\sigma` at $`m`. Consequently, for all sufficiently large $`h,m`, 

$$`\frac{[z^{m-j}]F_h(z)}{[z^m]F_h(z)}
 =x^j\frac{\mathbb P_x(N=m-j)}{\mathbb P_x(N=m)}
 \le Cx^j\qquad(0\le j\le m).`

 Only the denominator uses the local limit; the numerator may be at any index, including zero.

Let $`N_{k,L}` count curves of type $`k` with length at most $`L`, and put $`a_k=V_{0,k+1}/(k!P^{k-2})`. Mirzakhani integration gives 

$$`\begin{aligned}
 \mathbb E N_{k,L}=\frac{\binom nk}{V_{g,n}}
 \int_0^L\ell\,V_{0,k+1}(\ell,0^k)
                  V_{g,n-k+1}(\ell,0^{n-k})\,\mathrm{d}\ell,\\
 \binom nk\frac{V_{0,k+1}V_{g,n-k+1}}{V_{g,n}}
 =\frac nP a_k\frac{[z^{n-k}]F_h}{[z^{n-1}]F_h}.
 \end{aligned}`

 The two sides have different genera, so there is no side-exchange factor. The coefficient identity follows from 9.17; it holds up to $`k=n`. Bound 14.7 changes the integrand’s two volumes by a factor between one and $`\mathrm{e}^L`, independently of $`k`. Using 14.9 with $`j=k-1` therefore gives, for each fixed $`T`, 

$$`\mathbb E\sum_{k\ge K}N_{k,T/\sqrt{q_g^*}}
 \le CT^2\sum_{k\ge K}a_kx_c^{k-2}\longrightarrow0
 \quad(K\to\infty),`

 uniformly along the sequence. To justify summability directly, the genus-zero string solution gives $`\Phi_0'''(x)=1/a(Y(x))=Y'(x)`. Since $`V_{0,3}=1`, its zero initial conditions give $`\Phi_0''=Y` and $`\Phi_0'(x)=\int_0^xY(u)\,\mathrm{d}u`. This is finite at $`x_c`; positivity gives convergence of the coefficient series there. Its initial term $`x^2/2` also gives $`W(0)=1`.

Step 2: fixed types and nested configurations. Next we compute the mixed factorial moments for finitely many fixed cusp types. The main contribution comes from configurations whose planar sides are pairwise disjoint, which we call stars; nested configurations are shown to be negligible. Fix $`r` ordered distinct curves of prescribed types $`k_1,\ldots,k_r`, and write $`K=\sum k_i`. The collar lemma makes their boundaries disjoint. For a star, the ordered cusp-label multiplicity is $`(n)_K/\prod_i k_i!`, and the complement has type $`(g,n-K+r)`. There is no $`r!` divisor. The boundary error is $`1+O_r(L)`, as each cut occurs twice in 14.7. For fixed $`d`, 14.8 and $`q_g^*/q_g\to1` give $`V_{g,n-d}/V_{g,n}=(x/(Pn))^d(1+o(1))`. Thus for windows $`[a_i,b_i]/\sqrt{q_g^*}` the star contribution tends to 

$$`\prod_{i=1}^r
       w_{k_i}(x_\lambda)(b_i^2-a_i^2).`

 The positive expression has a relative error before taking the limit, even when some limiting weights vanish.

Filling cusps turns each planar side into a disk. Disjoint boundaries therefore have nested or disjoint disks; their cut graph is a tree with one genus-$`g` root and $`r` planar vertices. Let $`d` be the root degree, $`a_v` the number of cusps at a planar vertex and $`d_v` its degree; put $`a=\sum_v a_v`. Prescribed types bound $`a` by $`K`. There are finitely many such trees with ordered edges and cusp allocations, depending only on the fixed types. Classification of surfaces gives the corresponding mapping-class orbits with bounded symmetry factors; assigning cusp labels costs at most $`Cn^a`. The root volume ratio is $`O((x/(Pn))^{a-d})`, the planar volumes are fixed, and the $`r` length integrals cost $`O((nx)^{-r})`. Each cut type contributes at most 

$$`Cn^{d-r}x^{a-d-r}=O(n^{-1})\quad\hbox{if it is not a star}.`

 Indeed stability gives $`a_v+d_v\ge3` and $`\sum_vd_v=2r-d`, hence $`a\ge r+d`. The power of $`x` is nonnegative, so no loss occurs as $`x\to0`. A nonstar has $`d\le r-1`; if $`d=r`, every planar vertex is a leaf and the configuration is a star. This accounts for every fixed-type mixed factorial moment.

The limits 14.12 are the mixed factorial moments of independent Poisson counts. Higher fixed moments give uniform integrability, and the product Poisson law is moment determinate. First moments give tightness on compact sets in the marked space. This proves 14.4. Its unmarked projection requires more than vague convergence: truncate the types, pass to the finite-type limit, then let the cutoff grow using 14.11 and the convergent limiting series. This proves the stated unmarked process. Finally replace $`q_g^*` by $`q_g`. The type-two restriction gives 14.2 without assuming a limit for $`n/g`, by subsequences and compactness of $`[0,\infty]`. Its zero-count probabilities give the pants minimum law.

Step 3: the remaining curves and the systole. It remains to show that, on the scale $`q_g^{-1/2}`, there are no short curves other than planar separating ones: nonseparating curves, and separating curves with positive genus on both sides, are rare. Nonseparating simple curves of length at most $`L\le L_0` have expected count at most $`C\mathrm{e}^LL^2V_{g-1,n+2}/V_{g,n}\le CL^2`, by integration, 14.7, and the uniform lower bound for $`B_{g,n}`. To sum every positive-genus separating cut, put $`S_g(z)=\sum_{i=1}^{g-1}\Phi_i'(z)\Phi_{g-i}'(z)`. Exact positivity 9.1 includes genus one, so the child powers add to $`h-1`: 

$$`S_g(z)=V(z)^{h-1}Q_g(z),\qquad Q_g\ge0
 \ \hbox{coefficientwise},\qquad
 \frac{S_g(x)}{F_h(x)}\le\frac{Ca(Y)r(Y)^2}{g^2}.`

 The last bound is 6.18: undoing {bpref "eq:TL9"}[6.1] leaves exactly $`ar^2`, as the child complexities sum to $`2g-2` and their deficits to $`3g-4`. In particular bounded child genera are retained. Lemma {bpref "lem:point-mass"}[9.3], applied to the positive factor $`V^{h-1}`, gives $`\sup_j\mathbb P_x^{S}(N=j)\le C/\sigma`. Against the parent lower bound $`\mathbb P_x^{F}(N=n-1)\ge c/\sigma`, the standard deviations cancel. The coefficient identity 9.17 therefore yields 

$$`\begin{aligned}
 \mathcal A_{g,n}
 &:=\sum_{i=1}^{g-1}\sum_{k=0}^n\binom nk
       \frac{V_{i,k+1}V_{g-i,n-k+1}}{V_{g,n}}
   =\frac1P\frac{[z^n]S_g(z)}{[z^n]\Phi_g(z)}\\
 &=\frac{n}{Px}\frac{S_g(x)}{F_h(x)}
       \frac{\mathbb P_x^S(N=n)}{\mathbb P_x^F(N=n-1)}
   \le\frac{Cnar^2}{xg^2}\le\frac Cg.
 \end{aligned}`

 Indeed $`(n-1)/x=h/(Aar)`, while $`A` is bounded below and $`r` above. Thus no small-density factor is lost. Each separating orbit with two positive genera occurs in this ordered sum. Its integration symmetry and one-handle factors are at most one; applying 14.7 to both components bounds its total expected count by $`C\mathrm{e}^LL^2\mathcal A_{g,n}\le CL^2/g`. This includes all cusp partitions.

For fixed $`T`, take $`L=T/\sqrt{q_g}`. Markov’s inequality shows that with probability $`1-O(T^2/q_g)` every simple geodesic in this window is planar. Primitive geodesics shorter than $`2\operatorname{arcsinh}1` are simple, by the standard collar theorem used in \[41\] Section 1.1. Since $`q_g\to\infty`, the full primitive process and planar process agree on each bounded rescaled window with probability tending to one. This transfers the process limit and its zero-count law to the systole.

Finally restrict the first point to $`[\eta,T]` and finitely many cusp types. The first-point map is continuous when its first length is unique and avoids the endpoints, as happens almost surely in the limiting Poisson process. Let the type cutoff grow using 14.11, then $`\eta\downarrow0` and $`T\to\infty`. The omitted length probabilities tend to zero by the zero-count law; $`W\ge1`. Nonplanar competitors are excluded on each fixed window. This also makes any tie rule immaterial and proves planarity of every systolic curve with probability tending to one. The first-arrival density of the limiting marked process is 14.5.
:::



## Many small eigenvalues

:::proposition "prop:pants-concentration" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP3, eq:PS1")
%%%
source := { document := "paper-v3", spans := #[{ page := "62", anchor := "prop:pants-concentration", citation := "Proposition 14.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 14.2 — Many short pants.

Scope from Section 14.2: integer cusp counts, genus tending to infinity, and $`n/\sqrt g\to\infty`. All further hypotheses in the statement apply as written.

If $`L=L_g\to0` and $`q_gL_g^2\to\infty`, then 

$$`\frac{N_{L_g}}{q_gL_g^2}\longrightarrow1
 \quad\hbox{in probability}.`

 Consequently, for each fixed $`\varepsilon\in(0,1)`, with probability tending to one there are at least $`\lfloor(1-\varepsilon)q_gL_g^2\rfloor-1` positive discrete eigenvalues in $`(0,6L_g]`, counted with multiplicity.
:::



:::proof "prop:pants-concentration" (uses := "eq:PS3, thm:volume, ext:minmax")
The first two cases of {bpref "eq:PS3"}[14.6] give 

$$`m_L:=\mathbb E N_L=\frac{(n)_2L^2}{4}
       \frac{V_{g,n-1}}{V_{g,n}}(1+O(L))\sim q_gL^2,`

 and 

$$`\frac{\mathbb E(N_L)_2}{m_L^2}
 =\frac{(n-2)(n-3)}{n(n-1)}D_{g,n-1}^{-1}(1+O(L))\longrightarrow1.`

 Since $`m_L\to\infty`, the relative variance tends to zero, proving 14.16. This second-moment argument does not use the point-process limit at a window growing with $`g`.

Hide–Thomas \[41\] Lemma 5.3 prove that $`N` such pants boundaries of length at most $`L` give $`N-1` positive eigenvalues below $`6L`, provided $`6L<1/4`. For the reader’s convenience we recall the variational argument. Inside each pants choose a function equal to inward distance $`\rho` on the half-collar $`0\le\rho\le1`, equal to one beyond it, and zero outside the pants. For all sufficiently small boundary lengths $`\ell`, the collar lemma supplies this embedded half-collar. The function lies in $`H^1(X)`, and 

$$`\int|\nabla f|^2=\ell\sinh1,\qquad
 \int|f|^2\ge2\pi-\ell\sinh1.`

 Different pants have disjoint supports up to their boundaries, so the span of these functions has dimension $`N` and Rayleigh quotient at most $`6L` for small $`L`. Its intersection with the orthogonal complement of constants has dimension at least $`N-1`. Since the essential spectrum starts at $`1/4`, the form version of min–max gives the claimed positive discrete eigenvalues. Apply 14.16 and let $`g` grow.
:::



:::corollary "cor:many-spectrum" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP3, eq:PS1")
%%%
source := { document := "paper-v3", spans := #[{ page := "62", anchor := "cor:many-spectrum", citation := "Corollary 14.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Corollary 14.3 — A growing number of small eigenvalues.

Suppose $`g\to\infty` and $`n/\sqrt g\to\infty`. If $`j=j(g)\to\infty` and $`j=o(q_g)`, then 

$$`\mathbb P^{\mathrm{WP}}_{g,n}
 \{\lambda_j(X)\text{ exists and }\lambda_j(X)\le12\sqrt{j/q_g}\}
 \longrightarrow1,`

 where positive discrete eigenvalues are ordered with multiplicity.
:::



:::proof "cor:many-spectrum" (uses := "prop:pants-concentration")
For $`j\to\infty` with $`j=o(q_g)`, choose $`L_g=2\sqrt{j/q_g}`. Then $`L_g\to0`, $`q_gL_g^2=4j`, and 14.16 implies $`N_{L_g}\ge j+1` with probability tending to one. The preceding variational estimate gives $`\lambda_j\le6L_g=12\sqrt{j/q_g}`.
:::



The spectral mechanism is established in the fixed-genus work of Hide–Thomas \[41\] Theorem 1.10 and Remark 5.5; their later bordered-volume asymptotics give linear counts below each fixed positive threshold at fixed genus \[40\] Theorem 1.1. Their deterministic result \[42\] Theorem 1.3, in the July 2026 revision, gives a linear number below $`1/4` whenever $`g<an` for fixed $`a>0`. Our threshold tends to zero and the genus grows. In the range $`\sqrt g\ll n\ll g`, the corresponding second-moment volume inputs already follow from Shen–Wu \[79\]. The extension supplied here is the density-dependent intensity and removal of the upper restriction on $`n/g`. No sharp eigenvalue asymptotic, matching lower bound, or Poisson eigenvalue law is asserted.

## The tight length spectrum

We now consider curves that remain noncontractible after filling all cusps. The corresponding tight Weil–Petersson volumes were introduced by Budd \[11\]. Following Budd and Lions \[13\], a closed geodesic is tight if it is the unique shortest representative of its free homotopy class on the filled surface. The distinction matters: several ordinary geodesics can belong to the same class after the cusps are filled. The tight integration formula and the geometric argument used in the proof are due to \[13\]; the new input is a volume estimate that allows arbitrary prescribed cusp counts.

Let $`Y_\lambda` satisfy $`\lambda(Y_\lambda)=\lambda`, as in Proposition {bpref "prop:bounded-boundaries"}[9.4], and set

:::definition "eq:tight-scale" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:SP1")
%%%
source := { document := "paper-v3", spans := #[{ page := "63", anchor := "eq:tight-scale", citation := "Equation 14.17", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 14.17 — Tight length scale and limiting intensity.

In the setup and notation of this section, the paper defines or asserts:



$$`\alpha(\lambda)=\frac{\sqrt{2r(Y_\lambda)}}\pi,
 \qquad \nu(\mathrm dt)=\frac{\cosh t-1}{t}\,\mathrm dt.`


:::



Here $`\alpha(0)=1`, and the density of $`\nu` is defined to be zero at the origin.

:::theorem "thm:tight-spectrum" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP2, eq:tight-scale")
%%%
source := { document := "paper-v3", spans := #[{ page := "63", anchor := "thm:tight-spectrum", citation := "Theorem 14.4", pdf := some { path := "source/paper.pdf" } }] }
%%%

Theorem 14.4 — Tight lengths at arbitrary cusp density.

Let $`n=n(g)\ge0` be any integer sequence, and let $`X` have law $`\mathbb P^{\mathrm{WP}}_{g,n}`. As $`g\to\infty`, the point process 

$$`\sum_{\substack{\gamma\text{ primitive, unoriented}\\
                  \gamma\text{ tight on }X}}
 \delta_{\alpha(n/g)\ell_X(\gamma)}
 \ \Longrightarrow\ \operatorname{PPP}(\nu)`

 converges in distribution for the vague topology on $`[0,\infty)`. For every fixed $`L<\infty`, with probability tending to one all the curves counted in $`[0,L]` are simple, pairwise disjoint, and have connected complement after filling the cusps.
:::



In particular, no limit of $`n/g` is required. At large density, the endpoint expansion of $`r` gives 

$$`\alpha(\lambda)\sim
 \frac{\sqrt{3j_{0,1}\sqrt5}}\pi\lambda^{-1/4}.`

 This agrees with the scale in \[13\] Corollary 1.3. Budd and Lions asked whether their limit persists for other cusp weights and under the fixed-count measures $`\mathbb P^{\mathrm{WP}}_{g,n}` \[13\] Open Question 1.6. Theorem {bpref "thm:tight-spectrum"}[14.4] treats the fixed-count part of this question; Corollary {bpref "cor:tight-boltzmann"}[14.5] below treats the remaining cusp-weight regimes. The planar curves in Theorem {bpref "thm:pants-poisson"}[14.1] are contractible after filling the cusps and therefore do not occur in 14.18.

The proof follows the moment method of Budd and Lions. Their tight integration formula \[13\] Proposition 3.2 expresses factorial moments of tight curve counts through tight volumes of the cut surfaces. We first write the generating functions of tight volumes through the shifted amplitudes of Section 4 (Lemma {bpref "lem:tight-gf"}[F.1]); then extract the coefficient at the prescribed cusp count, as in Section 9 (Lemma {bpref "lem:tight-connected"}[F.2]); then show that configurations with disconnected complement are negligible (Lemma {bpref "lem:tight-separating"}[F.3]); and finally identify the Poisson limit (Subsection F.4). These steps are carried out in Appendix F.

Random cusp counts. For $`0\le\mu<\mu_{\rm cr}=x_c/(2\pi^2)`, the Boltzmann measure $`\mathbb P^{\mathrm{WP}}_{g,\mu}` first chooses the cusp count $`N` with probabilities proportional to $`\mu^nV_{g,n}/n!`, then samples $`\mathbb P^{\mathrm{WP}}_{g,n}` conditionally on $`N=n`. Its probability generating function is $`\Phi_g(2\pi^2\mu z)/\Phi_g(2\pi^2\mu)`, as in \[13\].

:::corollary "cor:tight-boltzmann" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP2, eq:tight-scale")
%%%
source := { document := "paper-v3", spans := #[{ page := "63", anchor := "cor:tight-boltzmann", citation := "Corollary 14.5", pdf := some { path := "source/paper.pdf" } }] }
%%%

Corollary 14.5 — Arbitrary subcritical cusp weights.

For any sequence $`0\le\mu_g<\mu_{\rm cr}`, put 

$$`a_g=\frac{\sqrt{2r(Y(2\pi^2\mu_g))}}\pi.`

 Under $`\mathbb P^{\mathrm{WP}}_{g,\mu_g}`, the primitive tight lengths multiplied by $`a_g` converge to $`\operatorname{PPP}(\nu)`. In particular, if $`\mu_g\to\mu<\mu_{\rm cr}`, the unscaled lengths have limiting intensity $`(\cosh(a_\mu t)-1)\,\mathrm dt/t`, where $`a_\mu=\sqrt{2r(Y(2\pi^2\mu))}/\pi`. If $`\mu_g\to\mu_{\rm cr}`, no condition on the speed of convergence is required.
:::



The proof is given in Subsection F.5.

## The full length spectrum at the critical cusp scale

The tight spectrum omits curves that become contractible when the cusps are filled. At $`n\asymp\sqrt g`, these curves contribute on the same length scale as the nonseparating curves. Their contribution is not Poisson: a two-cusp pair of pants contributes its whole length spectrum, not only its boundary.

For $`s>0`, let $`P_s` be the hyperbolic pair of pants with two cusps and one geodesic boundary of length $`s`. Write $`K_s` for its primitive unoriented length counting measure, including the boundary once and excluding parabolic classes. Equal lengths are counted with their geometric multiplicities. Let

:::definition "eq:cluster-intensities" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "def:wp-volume")
%%%
source := { document := "paper-v3", spans := #[{ page := "64", anchor := "eq:cluster-intensities", citation := "Equation 14.19", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 14.19 — Critical primitive cluster intensities.

In the setup and notation of this section, the paper defines or asserts:



$$`\mu_c(\mathrm ds)=\frac{c^2}{8\pi^2}\sinh(s/2)\,\mathrm ds,
 \qquad \nu(\mathrm dt)=\frac{\cosh t-1}{t}\,\mathrm dt.`


:::



:::theorem "thm:critical-cluster" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP3, eq:cluster-intensities")
%%%
source := { document := "paper-v3", spans := #[{ page := "64", anchor := "thm:critical-cluster", citation := "Theorem 14.6", pdf := some { path := "source/paper.pdf" } }] }
%%%

Theorem 14.6 — Critical primitive length spectrum.

Suppose $`g\to\infty` and $`n/\sqrt g\to c\in(0,\infty)`, and let $`X` have law $`\mathbb P^{\mathrm{WP}}_{g,n}`. Then 

$$`\sum_{\substack{\gamma\text{ primitive}\\\text{unoriented on }X}}
       \delta_{\ell_X(\gamma)}
 \ \Longrightarrow\ \Xi_c:=\mathcal N+\sum_{s\in\mathcal Q_c}K_s,`

 as locally finite counting measures on $`[0,\infty)` with the vague topology. Here $`\mathcal N` and $`\mathcal Q_c` are independent Poisson point processes of intensities $`\nu` and $`\mu_c`. In particular, for every nonnegative continuous compactly supported function $`f`, 

$$`\mathbb E\mathrm e^{-\langle f,\Xi_c\rangle}
 =\exp\left\{-\int(1-\mathrm e^{-f(t)})\,\nu(\mathrm dt)
 -\int(1-\mathrm e^{-\langle f,K_s\rangle})\,\mu_c(\mathrm ds)\right\}.`


:::



Shen and Wu obtained the factorial-moment asymptotics for short two-cusp pants and the limiting probability that such a curve occurs at this cusp scale \[79\] Lemmas 28 and 33. The corresponding Poisson mean is $`\mu_c([0,L])=c^2(\cosh(L/2)-1)/(4\pi^2)` on their stated short window. Theorem {bpref "thm:critical-cluster"}[14.6] concerns the full primitive process on every fixed length window, including the correlated lengths inside each pair of pants. The background intensity and the geometric moment method come from Mirzakhani and Petri \[65\]. The critical regime needs the volume bounds of Mirzakhani–Zograf and Shen–Wu \[66\]; \[79\] together with the zero-density case of Theorem {bpref "thm:volume"}[1.3] and Proposition {bpref "prop:bounded-boundaries"}[9.4]: at $`n\asymp\sqrt g` the earlier estimates bound the genus ratio $`V_{g-1,n+2}/V_{g,n}` only from above. The full uniform expansion is not used.

The nonsimple part distinguishes this regime from closed surfaces. He, Shen, Wu and Xue proved that the nonsimple systole of a Weil–Petersson random closed surface is asymptotic to $`\log g`, with a more precise concentration about $`\log g-\log\log g` \[35\] Theorem 1.1. Thus nonsimple curves leave every fixed length window in that model. At the critical cusp scale here, two-cusp pants instead retain nonsimple curves of bounded length.

Outline of the proof. Short multicurves are organized by their cut graphs. Using only the volume bounds of \[66\]; \[79\], Lemma {bpref "lem:critical-cuts"}[G.1] shows that in the limit a cut graph contributes only if it has one component carrying the genus, possibly with nonseparating loops, and two-cusp pairs of pants attached to it as leaves. A bounded-multiplicity argument (Lemmas {bpref "lem:primitive-count"}[G.2] and {bpref "lem:critical-complex"}[G.3]) reduces intersecting simple curves and nonsimple curves to such cut graphs; hence, with probability tending to one, every short nonsimple curve lies in a two-cusp pair of pants. The mixed factorial moments of nonseparating lengths and pants waists converge to those of independent Poisson processes (Lemma {bpref "lem:critical-skeleton"}[G.4], where the zero-density volume ratios enter), and attaching to each waist the full spectrum of its pair of pants gives $`\Xi_c`. The details are given in Appendix G.

:::lemma_ "eq:cluster-overdispersion" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "thm:critical-cluster, lem:primitive-count, eq:cluster-intensities")
%%%
source := { document := "paper-v3", spans := #[{ page := "64", anchor := "eq:cluster-overdispersion", citation := "Equation 14.22", pdf := some { path := "source/paper.pdf" } }, { page := "65", anchor := "eq:cluster-overdispersion", citation := "Strict positivity and non-Poisson deduction following Equation 14.22", pdf := some { path := "source/paper.pdf" } }] }
%%%

Equation 14.22 and its subsequent deduction — finite moments and non-Poisson critical clusters.

This is a paper-new deduction, not a separately numbered lemma in the original paper. The conditional Lean proof uses the canonical pants spectrum and the same independent Poisson product law as Theorem 14.6. Classical inputs are Campbell’s formulas and Rivin’s figure-eight formula; the count bounds, variance excess and strict non-Poisson deduction are proved locally.

The limit is not Poisson. If $`m_L(s)=K_s([0,L])`, then Lemma {bpref "lem:primitive-count"}[G.2] and the support restriction $`s\le2L` give finite moments and 

$$`\operatorname{Var}\Xi_c([0,L])-\mathbb E\Xi_c([0,L])
 =\int m_L(s)(m_L(s)-1)\,\mu_c(\mathrm ds).`

 Besides its waist, $`P_s` contains the primitive figure-eight around its two cusps, of length $`2\operatorname{arccosh}(2+\cosh(s/2))` by \[76\] Theorem 1.3. For $`L>2\operatorname{arccosh}3`, both lengths lie below $`L` on an interval of positive $`\mu_c`-measure. The right side of 14.22 is therefore strictly positive. The theorem identifies these correlations in the limit; no convergence of the full-spectrum second moments is asserted.

:::
