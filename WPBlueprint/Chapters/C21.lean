import WPBlueprint.Chapters.C20
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "appF-tight-proofs" =>

# Proofs for the tight length spectrum

This appendix proves Theorem {bpref "thm:tight-spectrum"}[14.4] and Corollary {bpref "cor:tight-boltzmann"}[14.5], following the outline in Subsection 14.4. The scale $`\alpha` and the intensity $`\nu` are those of {bpref "eq:tight-scale"}[14.17].

## Tight volume generating functions

Put $`P=2\pi^2`. Let $`T_{g,p,k}(\mathbf L)` be the tight volume with $`p` protected geodesic boundaries and $`k` cusps that may be filled, in the conventions of \[11\]; \[14\]; \[13\]. For stable $`(g,p)` define 

$$`\mathscr T_{g,p}(x;\mathbf L)
 =\sum_{k\ge0}\frac{T_{g,p,k}(\mathbf L)}{P^{3g-3+p+k}}
                 \frac{x^k}{k!},\qquad F_{g,p}=\Phi_g^{(p)}.`

 Unmarked functions are used only for $`g\ge2`. Set $`\varrho(Y)=\sqrt{r(Y)/P}` and $`S(t)=\sinh(t)/t`, with $`S(0)=1`.

:::lemma_ "lem:tight-gf" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "100", anchor := "lem:tight-gf", citation := "Lemma F.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma F.1 — Tight generating functions.

Let $`(g,p)` be stable and $`0\le Y<y_0`. The tight generating function is expressed through the shifted amplitudes by the exact identity 

$$`\mathscr T_{g,p}(X(Y);\mathbf L)
 =\sum_{\mathbf d}U^Y_{g,p}(\mathbf d)
       \prod_{i=1}^p\frac{L_i^{2d_i}}{P^{d_i}(2d_i+1)!},`

 which fixes both the normalization and the meaning of the protected boundaries. Its ratio to the ordinary marked generating function satisfies 

$$`\begin{aligned}
 1\le\frac{\mathscr T_{g,p}(X(Y);\mathbf L)}{F_{g,p}(X(Y))}
   &\le\prod_{i=1}^p S(\varrho(Y)L_i),\\
 \frac{\mathscr T_{g,p}(X(Y);\mathbf L)}{F_{g,p}(X(Y))}
   &=\prod_{i=1}^p S(\varrho(Y)L_i)
        \bigl(1+O_{p,B}(g^{-1})\bigr)
       \quad\text{if }\max_i\varrho(Y)L_i\le B,
 \end{aligned}`

 where the inequality holds at every stable genus. Finally, for each fixed physical length vector, 

$$`\mathscr T_{g,p}(x;\mathbf L)=V(x)^{2g-2+p}R_{g,p,\mathbf L}(x),
 \qquad [x^j]R_{g,p,\mathbf L}(x)\ge0,`

 and the series converge for $`0\le x<x_c`.

Lean coverage (R26): the associated declarations prove the identity, bounds,
uniform relative error, and convergent positive factor for every stable
protected count, including p=0. The classical Budd--Zonneveld transform and
higher-kappa realization remain explicit inputs; their concrete geometric
instances have not been constructed.

:::



:::proof "lem:tight-gf" (uses := "ext:tight-transform, lem:convolution, lem:monotone, eq:TL23")
The identity F.1 follows from \[14\] Proposition 12. Indeed, their root and moments are $`R=Y/P` and $`M_j=P^jX^{(j+1)}(Y)`. With $`q=P/2`, their shifted times are $`q^{k-1}t'_k`, where the $`t'_k` are the times in {bpref "eq:H8"}[4.7]. The dimension constraint gives the factor $`q^{3g-3+p-|\mathbf d|}`. Combining their external insertion $`2L^{2d}/(4^d d!)` with the free-energy factor $`2^{3g-3}` and the double factorial in {bpref "eq:H6"}[4.5] gives F.1. This also covers genus zero with $`p\ge3`.

Equations 6.7 and {bpref "eq:TL23"}[6.15] give F.2. For the asymptotic estimate, the factorial series with the extra weight $`|\mathbf d|(|\mathbf d|+1)` is uniformly summable on the indicated box. Thus the lengths may grow as $`r(Y)^{-1/2}`.

For each fixed physical length vector, the proof of 9.1 applies to every amplitude in F.1, which gives F.3. The finite sum in F.1 and F.2 justify convergence throughout $`0\le x<x_c`.
:::



## Prescribing the cusp count

We record the coefficient argument for the cut surfaces that occur in the tight integration formula. Fix a number $`k` of cuts and put $`h_0=2g-2`. When $`n\to\infty`, choose $`x` by 

$$`(h_0+1)\Psi(x)=n-1,\qquad
 \sigma^2=(h_0+1)\mathscr D\Psi(x),\qquad x=X(Y),`

 and write $`\alpha_x=2\varrho(Y)`. If $`n` stays bounded, we pass to a subsequence on which $`n` is fixed and take instead $`x=c/h_0` with $`c>0`.

:::lemma_ "lem:tight-connected" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP2")
%%%
source := { document := "paper-v3", spans := #[{ page := "101", anchor := "lem:tight-connected", citation := "Lemma F.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma F.2 — Connected cut configurations.

Fix $`k` and a compact box of scaled lengths $`\mathbf t\in[0,\infty)^{2k}`. With $`x` chosen as above, uniformly for $`\mathbf t` in the box, 

$$`\frac{[z^n]\mathscr T_{g-k,2k}(z;\mathbf t/\alpha_x)}
      {[z^n]\Phi_g(z)}
 =(4r(Y))^k\prod_{i=1}^{2k}S(t_i/2)(1+o(1)).`

 Moreover $`\alpha_x/\alpha(n/g)\to1`.
:::



:::proof "lem:tight-connected" (uses := "lem:tight-gf, prop:local-limit, prop:marked-ratios")
Suppose first that $`n\to\infty`. The denominator $`F_{g,1}=\Phi_g'` has its local limit at $`n-1`. For the connected-complement numerator $`G(x)=\mathscr T_{g-k,2k}(x;\mathbf t/\alpha_x)`, the physical lengths are held fixed when its argument is varied. Its model center is $`h_0\Psi(x)`, and 

$$`\frac{n-h_0\Psi(x)}\sigma
 =\frac{1+\Psi(x)}\sigma\longrightarrow0.`

 The endpoint expansions give 

$$`\sup_{0<x<x_c}
 \frac{|\mathscr D\log r(Y(x))|}{\sqrt{\mathscr D\Psi(x)}}<\infty.`

 Consequently a real tilt $`x\mathrm e^{u/\sigma}` changes $`r` by a relative $`O_u(g^{-1/2})`, uniformly up to either endpoint. Equation F.2 therefore transfers the real Gaussian limit from $`F_{g-k,2k}` to $`G`. The positive factor F.3 transfers the Fourier estimates 9.8–9.14. The two local probabilities at $`n` and $`n-1` are asymptotic to $`(\sqrt{2\pi}\sigma)^{-1}`.

We use the derivative only in the denominator: adding a protected cusp to a tight surface would change which homotopies are allowed. For a generating function $`J` with nonnegative coefficients write $`\mathbb P_x^J(N=m)=[z^m]J(z)x^m/J(x)`. The exact identity is 

$$`\frac{[z^n]G(z)}{[z^n]\Phi_g(z)}
 =\frac n x\frac{G(x)}{\Phi_g'(x)}
       \frac{\mathbb P_x^G(N=n)}
            {\mathbb P_x^{\Phi_g'}(N=n-1)}.`

 Equation {bpref "eq:TL24"}[6.16] at $`p=0` shows that $`n\Phi_g(x)/(x\Phi_g'(x))\to1`. Iterating 6.21 now yields F.4.

For bounded $`n`, with $`x=c/h_0`, equation {bpref "eq:TL24"}[6.16] gives 6.20 also at $`p=0`. Integrating that estimate between $`x` and $`xz`, and using $`\Psi(x)=2x+O(x^2)`, proves convergence of the probability generating functions to $`\exp(2c(z-1))`. The same holds for $`G` by F.2. The probabilities at the fixed index $`n` thus converge to the same positive Poisson probability. This proves F.4 in this case too.

Finally $`\alpha_x/\alpha(n/g)\to1`. At finite density this follows by continuity; at infinite density use $`r(Y_\lambda)\sim
(3\sqrt5j_{0,1}/2)\lambda^{-1/2}`. This relative comparison is needed because both scales tend to zero at infinite density.
:::



## Separating configurations

:::lemma_ "lem:tight-separating" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP2")
%%%
source := { document := "paper-v3", spans := #[{ page := "101", anchor := "lem:tight-separating", citation := "Lemma F.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma F.3 — Separating configurations.

Fix $`k` and $`L`. Uniformly in $`n`, with lengths scaled by $`\alpha_x`, 

$$`\mathbb E^{\mathrm{WP}}_{g,n}
 \bigl[\text{ordered separating tight $k$-tuples with scaled
 lengths at most $L$}\bigr]=o(1),`

 where only simple, pairwise disjoint tuples are counted, and separating means that their union disconnects the filled surface.
:::



:::proof "lem:tight-separating" (uses := "lem:tight-gf, lem:point-mass, prop:prefactor")
For a stable connected cut graph with $`k` edges and $`Q` vertices, let $`(g_i,p_i)` be the component types after filling the cusps. Then 

$$`p_i\ge1,\quad h_i=2g_i-2+p_i\ge1,\quad
 \sum_i h_i=h_0,\quad \sum_i p_i=2k,\quad
 \sum_i g_i=g-k+Q-1.`

 For fixed positive $`p`, Proposition {bpref "prop:prefactor"}[7.1] implies the two-sided bound 

$$`F_{g,p}(X(Y))\asymp_p
 4^{-g}\mathcal Z(Y)^{-h}r(Y)^{p/2}f(h),
 \qquad f(h)=\frac{\Gamma(h)}{\sqrt h},\quad h=2g-2+p.`

 The constants are uniform in $`Y`. Bounded stable genera are included by positivity and continuity of the normalized finite amplitudes on $`[0,y_0]`. For $`p=0`, $`g\ge2`, the same bound follows from $`p=1` and {bpref "eq:TL24"}[6.16].

The identities for the component types cancel all powers of $`\mathcal Z` in the product-to-parent ratio. They leave 

$$`r(Y)^{-k}\frac{\prod_i F_{g_i,p_i}(X(Y))}{\Phi_g(X(Y))}
 \le C_k\frac{\prod_i f(h_i)}{f(h_0)}.`

 To sum over genera, observe that $`\sum_{a=1}^{\ell-1}f(a)f(\ell-a)\le C f(\ell-1)`. Indeed, 

$$`\frac{\Gamma(a)\Gamma(\ell-a)}{\Gamma(\ell)}
 =\frac{1}{(\ell-1)\binom{\ell-2}{a-1}},`

 the reciprocal binomial coefficients have uniformly bounded sum, and $`\sqrt{\ell}/\sqrt{a(\ell-a)}` is bounded. Iteration gives $`f^{*Q}(\ell)\le C_Q f(\ell-Q+1)`. Since the marking allocations and gluings have bounded multiplicity for fixed $`k`, it follows that 

$$`r(Y)^{-k}\sum_{\substack{\text{stable cut types}\\Q\text{ components}}}
 \frac{\prod_i F_{g_i,p_i}(X(Y))}{\Phi_g(X(Y))}
 \le C_k g^{-(Q-1)},\qquad 2\le Q\le k+1.`



For scaled lengths in a fixed compact box, F.2 bounds each boundary factor uniformly, including on small-genus components. Every product in this positive sum has the factor $`V^{h_0}` by F.3. Its largest tilted point probability is at most $`C/\sigma`, by Lemma {bpref "lem:point-mass"}[9.3]. Applying F.5, against the denominator probability at least $`c/\sigma`, therefore transfers F.8 to coefficients. For bounded $`n`, use $`x=c/h_0` and the positive limiting denominator probability; the numerator probability is at most one.

In the tight integration formula \[13\] Proposition 3.2, the physical normalization costs $`P^{-k}` and the length Jacobian is $`\alpha_x^{-2k}=(P/(4r))^k`. These cancel the remaining $`r^k`. The symmetry factors are at most one. This proves F.6.
:::



## Proof of Theorem {bpref "thm:tight-spectrum"}[14.4]

:::proof "thm:tight-spectrum" (uses := "lem:tight-connected, lem:tight-separating, ext:tight-integration, ext:tight-geometry")
For fixed disjoint intervals in $`(0,\infty)`, count ordered tuples of simple, pairwise disjoint tight curves in those intervals. The connected-complement symmetry is $`2^{-k}` in the tight integration formula. Lemma {bpref "lem:tight-connected"}[F.2], with each cut length appearing on two boundary components, gives the limiting integrand 

$$`\prod_{i=1}^k\frac12 t_i S(t_i/2)^2\,\mathrm dt_i
 =\prod_{i=1}^k\frac{\cosh t_i-1}{t_i}\,\mathrm dt_i.`

 Lemma {bpref "lem:tight-separating"}[F.3] removes all other cut types. Thus the disjoint-tuple moments have the Poisson limits of every fixed order.

Here the disjoint-tuple moments must be related to the actual count moments: a small probability of intersections alone would not suffice. Choose $`L` above all interval endpoints, and let $`A_L` be the event that scaled lengths at most $`L` include a self-intersecting tight curve or two intersecting tight curves. Write $`\widehat N_{\mathbf r}` for the disjoint-tuple count in the prescribed intervals, with multiplicities $`\mathbf r=(r_1,\ldots,r_j)`. We use the deterministic constructions in the proofs of \[13\] Propositions 5.2–5.3, rather than their probabilistic conclusions in the near-critical model. These constructions apply after rescaling by any positive length scale.

Fix $`\varepsilon>0` below the interval endpoints. On $`A_L`, outside the event of a tight systole shorter than $`\varepsilon`, the construction extends a counted tuple to a separating tight multicurve. Its number of components and scaled lengths are bounded in terms of $`\varepsilon,L,\mathbf r`, independently of $`g,n`. If there is a shorter tight systole, either it adds a disjoint curve in $`[0,\varepsilon]`, or the tuple again extends to a separating multicurve. The original ordered tuple is retained in these extensions. Thus the separating terms vanish by F.6, and the mixed disjoint-tuple limit gives 

$$`\limsup_{g\to\infty}\mathbb E[
   \widehat N_{\mathbf r}\mathbf1_{A_L}]
 \le \nu([0,\varepsilon])\prod_{i=1}^j\nu(I_i)^{r_i},`

 where $`I_i` are the prescribed intervals. Letting $`\varepsilon\downarrow0` removes the right side. The same construction without a marked tuple gives $`\mathbb P(A_L)\to0`. Conditional on $`A_L^c`, factorial counts are exactly disjoint-tuple counts. Their limiting moments therefore remain unchanged, and the moment-determinate Poisson law gives joint count convergence.

The first-moment bound for simple tight curves in $`[0,\varepsilon]` tends to $`\nu([0,\varepsilon])\to0`. A shortest tight curve is simple, so the same bound controls the event of any tight curve in this window. This extends the convergence to $`[0,\infty)` and gives tightness on compact intervals. Finally the disjoint-tuple moments bound the number of curves in a fixed window in probability. For any fixed upper bound on that number, F.6 rules out every disconnected complement. Letting the upper bound increase proves the last claim.
:::



## Proof of Corollary {bpref "cor:tight-boltzmann"}[14.5]

:::proof "cor:tight-boltzmann" (uses := "thm:tight-spectrum, prop:marked-ratios, lem:parameter")
Write $`x=P\mu_g` and $`h=2g-2`. The case $`x=0` has $`N=0`. Otherwise {bpref "eq:TL24"}[6.16] at $`p=0` gives 

$$`\mathbb E N=h\Psi(x)+O(\Psi(x)).`

 If $`h\Psi(x)` stays bounded, $`N` is tight and both $`N/g` and $`2\Psi(x)` tend to zero. If $`h\Psi(x)\to\infty`, integrating 6.20 at $`p=0` gives the same real central limit theorem as 9.6, hence 

$$`N=h\Psi(x)+O_{\mathbb P}\!\left(\sqrt{h\mathscr D\Psi(x)}\right).`

 The endpoint estimates 9.3 imply $`\mathscr D\Psi/\Psi^2\le C(1+1/\Psi)`. It follows that $`N/(h\Psi(x))\to1` in probability in this second case. Continuity of $`\alpha` at finite density and its $`\lambda^{-1/4}` asymptotic at infinity therefore give, in both cases, 

$$`\frac{\alpha(N/g)}{\alpha(2\Psi(x))}
 =\frac{\alpha(N/g)}{a_g}\longrightarrow1
 \quad\text{in probability}.`

 Subsequences cover arbitrary choices of $`x`.

For each fixed nonnegative compactly supported continuous test function, the conditional Laplace-functional convergence in Theorem {bpref "thm:tight-spectrum"}[14.4] is uniform in $`n`: a sequence violating uniformity would contradict that theorem. Averaging over $`N` gives the Poisson limit with random normalization $`\alpha(N/g)`. The displayed scale comparison and continuity of dilation of point measures replace this by $`a_g`. For $`\mu_g\to\mu<\mu_{\rm cr}`, a change of scale gives the stated unscaled intensity. At the critical endpoint, $`r\sim3(y_0-Y)` and $`x_c-x\sim(-X''(y_0))(y_0-Y)^2/2` show that $`a_g` is asymptotic to the scale in \[13\] Theorem 1.2.
:::


