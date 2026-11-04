import WPBlueprint.Chapters.C10
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "12-diagonal" =>

# The full diagonal chain

The absolute expansion assumes $`g\to\infty`. To reach the bounded-genus end of the diagonal chain, we instead sum the logarithms of the cusp ratios of Theorem {bpref "thm:volume"}[1.3] and compare with the fixed-genus asymptotics of Manin and Zograf. This proves Theorem {bpref "thm:chain"}[1.5], with $`F` as in {bpref "eq:WC1"}[1.8]. The result has only logarithmic precision, although the cusp ratios are known with relative errors: summing $`n` of their logarithms accumulates an error $`n\varepsilon_g` with $`\varepsilon_g\to0`.

We use the functions $`T,\Delta,I,J` and the profile $`\mathcal C` of Section 3, and the variable $`t=\lambda/(2+\lambda)\in[0,1)`; thus $`Y(u)` in {bpref "eq:WC1"}[1.8] is the parameter with $`\lambda=2u/(1-u)`.

:::proof "thm:chain" (uses := "thm:volume, lem:parameter, ext:fixed-genus, ext:fixed-cusps")
We first give a closed form for {bpref "eq:WC1"}[1.8]. From 3.1 and differentiation under the integral, 

$$`I'=-X'(Y)\sqrt\Delta,
 \qquad J'=-\frac{I\Delta'}{2\Delta^{3/2}}.`

 Writing $`t=\beta(Y)=X/J`, these identities show that 

$$`F(t)=-2\log(2J(Y))
      -(1-t)\log\frac{4\Delta(Y)}{\pi^2}`

 has derivative $`\log(4\Delta/\pi^2)`. Its value at zero is zero, because $`J(0)=1/2` and $`\Delta(0)=\pi^2/4`; hence it is precisely {bpref "eq:WC1"}[1.8]. As $`t\to1`, $`J\to x_c` and $`(1-t)\log\Delta\to0`, proving its stated continuous endpoint.

Set 

$$`Z_{g,n}=\frac{V_{g,n}}{(2g+n-3)!(4\pi^2)^{2g+n-3}},\qquad
 f(\lambda)=\log\frac{2\mathcal C(\lambda)}{4\pi^2(2+\lambda)}
            =-\log(2J(Y)).`

 Since $`J'>0`, $`f` decreases from zero to $`-\log(2x_c)` and has finite total variation. Equation 12.1 gives the exact identity 

$$`\int_0^\lambda f(v)\,\mathrm{d}v
   =\left(1+\frac\lambda2\right)
       F\left(\frac\lambda{2+\lambda}\right).`



For $`g\ge2`, the exact adjacent-cusp relation is 

$$`\log Z_{g,n}=\log Z_{g,0}
  +\sum_{j=0}^{n-1}
      \log\frac{2g C_{g,j}}{4\pi^2(2g+j-2)}.`

 Let $`\varepsilon_g\to0` bound the logarithmic error in the uniform $`C` profile. Replacing $`C` by $`\mathcal C`, and replacing $`2g+j-2` by $`2g+j`, gives total error $`O(n\varepsilon_g+1+\log(1+n/g))`. The bounded variation of $`f` gives the uniform Riemann-sum estimate 

$$`\sum_{j=0}^{n-1}f(j/g)
       =g\int_0^{n/g}f(v)\,\mathrm{d}v+O(1),`

 with a constant independent of $`n`. The fixed-cusp closed-volume asymptotic gives $`\log Z_{g,0}=o(g)`. Using 12.2, we obtain 

$$`\log Z_{g,n}
  =\frac{2g+n}{2}F\left(\frac{n}{2g+n}\right)+o(2g+n),`

 uniformly for all $`n` as $`g\to\infty`.

The same statement holds uniformly over all stable pairs with $`2g+n\to\infty`. To check the remaining case, keep $`g` fixed and use the fixed-genus leading cusp asymptotic \[58\] Section 6, which gives 

$$`\log Z_{g,n}=-n\log(2x_c)+O_g(\log(n+1)).`

 Meanwhile $`F(1)-F(t)=O((1-t)|\log(1-t)|)`, by 3.2, so the right side of 1.9 differs from the same leading term by only $`O_g(\log(n+1))`. Every sequence of stable pairs has a subsequence on which the genus is fixed or tends to infinity. This proves the full uniformity claimed for 1.9.

Along $`(g,n)=(G-j,2j)`, the value $`2g+n=2G` and the factorial normalization are constant. Subtracting the closed value $`\log Z_{G,0}=o(G)` from 1.9 proves 1.10, including $`j=0` and $`j=G`. This full-chain statement includes bounded genera, whereas the absolute equivalent in Theorem {bpref "thm:absolute"}[11.1] is uniform in cusp count as the genus tends to infinity.
:::


