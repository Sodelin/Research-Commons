# Grouping the centered low-modulus row at powers of two

Fix \(N=2^k\), \(L=\log N\), \(Q=N^{1/4}\), and \(\alpha=\sqrt N/L^{K_0}\) with \(K_0\) fixed in the corrected divisor comparison. This note keeps the **whole** centered row \(q<Q\), including its original strict \(m>\alpha q\) cutoff, and only makes selections on the reflected endpoint \(m=N-n\). Nothing here replaces a selection in the expanded center. The latest peer signed semiprime remainder uses the separate \(q,h\) center and a different prime-tested support. [Pinned pointwise ledger](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0) · [Strict moving-cut correction, Moya §§4–6](https://zenodo.org/records/21939906) · [Peer exact signed center](https://github.com/Sodelin/Research-Commons/commit/5dacecc2ceab3fc3c32a634ef5d0f21d4468000f)

## Exact grouping including the model

Let \(S=2\prod_{r>2}(1-(r-1)^{-2})=\mathfrak S(N)\). For \(m>N^{3/4}\) and squarefree odd \(m\), define
\[
 D_Q(m)=\sum_{\substack{q\mid m\\q<Q}}\mu(q)\log(m/q),\qquad
 a_Q(m)=\prod_{\substack{p\mid m\\p<Q}}p
\]
with the empty product equal to one. For every selection \(\mathcal A\) of such endpoints, the centered low row restricted to \(\mathcal A\) is
\[
 E_{\rm lo}(\mathcal A)
 =-\sum_{\substack{m\in\mathcal A\\m<N}}
 \Lambda(N-m)\mu(m)(D_Q(m)-S)+O(N e^{-c\sqrt L}L).
 \tag{1}
\]
Indeed all \(q<Q\) obey the strict \(\alpha q<m\) there, including the first integer endpoint above \(N^{3/4}\). Reversing the actual sum gives exactly \(-D_Q\). Reversing the model gives
\[
 \sum_{\substack{q<Q\\q\ {\rm odd}}}
 \frac{\mu(q)}{\varphi(q)}\log(q/m)
 =-\sum_{\substack{q<Q\\q\ {\rm odd}}}
 \frac{\mu(q)}{\varphi(q)}\log(Q/q)
 +\log(Q/m)\sum_{\substack{q<Q\\q\ {\rm odd}}}\frac{\mu(q)}{\varphi(q)}
 =-S+O(L e^{-c\sqrt L})
\]
by Goldston–Yıldırım's two truncated reciprocal estimates, in the form of Huang–Li Lemma 1. The strict \(q<Q\) evaluation uses the usual adjustment by at most \(\varphi(Q)^{-1}\) in the unweighted sum when \(Q\) is an integer. The weighted sum already has zero at \(q=Q\). The error in (1) uses only \(\sum_{n<N}\Lambda(n)\ll N\), so is uniform in \(\mathcal A\). Endpoints \(m\le N^{3/4}\) cost \(O_\epsilon(N^{3/4+\epsilon})\) on the original strict support using divisor multiplicity in the actual sum and \(\sum_{q<Q}1/\varphi(q)\ll L\) in the model. The squarefree condition retains every nonzero term because of \(\mu(m)\). Even \(m\) and proper prime powers on the \(n\) side together cost \(O_\epsilon(N^{1/2+\epsilon})\) by the same fixed-endpoint divisor cap. [Huang–Li Lemma 1](https://arxiv.org/pdf/2005.03811v2)

If \(a_Q(m)<Q\), the exact \(q\) support consists of all its divisors. Thus
\[
 D_Q(m)=
 \begin{cases}
 \log m,&a_Q(m)=1,\\
 \log p,&a_Q(m)=p\text{ a prime},\\
 0,&a_Q(m)\text{ has at least two prime factors}.
 \end{cases}
 \tag{2}
\]
For the last case both \(\sum_{q\mid a_Q}\mu(q)\) and \(\sum_{q\mid a_Q}\mu(q)\log q\) vanish. This is an actual-side cancellation. The centered row in (1) still has the \(S\mu(m)\Lambda(N-m)\) term on those endpoints.

There is also an exact way to spend the model and the entire low row together, without estimating that residual model term separately. If \(M_0(N)=S(N-\sum_{n<N}\Lambda(n)\mu(N-n))\), then (1) and the endpoint trims give
\[
 M_0(N)+E_{\rm lo}(N)
 =S N-\!\!\sum_{\substack{N^{3/4}<m<N\\m\ {\rm odd,\ squarefree}}}
        \Lambda(N-m)\mu(m)D_Q(m)+o(N).
 \tag{3}
\]
A budget based on (3) uses \(SN\) and the uncentered low row. It cannot also use the square-lane model margin as an independent summand. Conversely, (1) permits charging an isolated endpoint slice while keeping \(M_0\) as in the existing budget. These are exact choices of grouping at this target.

## A short product of the primes below \(Q\)

Fix \(2\le Y\le N^{1/8}\). The entire centered contribution with
\[
 1<a_Q(m)\le Y
\]
has absolute value
\[
 O\!\left(\frac{N(1+\log Y)}{L}\right)+O_\epsilon(N^{3/4+\epsilon}).
 \tag{4}
\]
In particular this is \(o(N)\) for \(\log Y=o(L)\), with the same \(M_0\), strict cutoff and full pre-grouping \(q\) range. To prove it, restrict first to \(m>N^{3/4}\), \(m\) odd and squarefree, and \(n=N-m\) an actual prime greater than \(N^{1/20}\). The excluded endpoint sums have the errors just proved, with the \(n\le N^{1/20}\) part bounded in the same fixed-endpoint way. Write \(m=a h\) with \(a=a_Q(m)\). Then \(h\) is \(Q\)-rough: all its primes are at least \(Q\). The exact coefficient \(D_Q-S\) in (1) is \(\log p-S\) if \(a=p\) is prime, and \(-S\) if \(a\) has at least two prime factors.

We need the uniform upper bound
\[
 \#\{1\le h<N/a:\ h\text{ is }Q\text{-rough},\ N-ah
       \text{ is prime }>N^{1/20}\}
 \ll \frac{N}{aL^2}\prod_{r\mid a}\left(1+\frac3r\right)
            +N^{1/10+o(1)}
 \tag{5}
\]
for an odd \(a\). Use an auxiliary upper Selberg square of level \(D=N^{1/20}\) on the product \(h(N-ah)\), with odd sieve primes at most \(D^c\) for a sufficiently small fixed \(c>0\). It equals one on the selected support, because both forms pass the sifting. At an odd \(r\nmid a\) there are exactly two forbidden residues for \(h\bmod r\), as \(N=2^k\). At \(r\mid a\) there is just \(h=0\bmod r\). Thus \(g(r)=2/r\) or \(1/r\), respectively. Put \(b(r)=g(r)/(1-g(r))\) for the Selberg diagonal. The full product \(\prod_{r\le D^c,\ r>2}(1+b(r))\) is bounded below by a fixed positive multiple of \(L^2/\prod_{r\mid a}(1+3/r)\): changing \(g(r)\) from \(2/r\) to \(1/r\) decreases the local factor by the ratio \((r-1)/(r-2)\le1+3/r\). The mass restricted to indices at most \(D\) is at least one half the full product for small enough \(c\). In fact the normalized Euler law has mean \(\sum_{r\le D^c}g(r)\log r\ll \log(D^c)\) for the log index, and Markov gives the claim. Hence its reciprocal diagonal norm is bounded by \(O(L^{-2}\prod_{r\mid a}(1+3/r))\). The optimal square has \(\lambda_1=1\) and \(|\lambda_d|\le1\), by the positive diagonal formula. After opening it, the number of residue classes for each least common multiple of two sieve indices is at most \(2^{\omega(\cdot)}=N^{o(1)}\), so the total floor error is \(D^2N^{o(1)}\). This proves (5). [Standard Selberg diagonal identity, pinned calculation](https://github.com/Sodelin/Research-Commons/commit/b8d0afa3e5fab3380f662ce172eacad56ea05316)

For prime \(a=p\), multiply (5) by \(O(L(1+\log p))\), and use \(\sum_{p\le Y}(1+\log p)/p\ll1+\log Y\). For composite \(a\), the coefficient is \(O(L)\) after multiplying by \(\Lambda(n)\). The reciprocal sum over these \(a\le Y\) is bounded by
\[
 \sum_{a\le Y}\frac1a\prod_{r\mid a}(1+3/r)
 \le (1+\log Y)\sum_{e\ge1}\frac{\mu^2(e)3^{\omega(e)}}{e^2}
 \ll 1+\log Y
\]
by expanding the product over \(e\mid a\). The total floor error is \(N^{1/10+1/8+o(1)}\) with the logs absorbed, smaller than the error in (4). All selections were made at fixed \(m\) before summing \(q\). In particular the bound does not follow from deleting the single \(q=p\) term, whose logarithm need not be small.

## Rough endpoints and a vanishing-width adverse slice

For \(a_Q(m)=1\), each prime factor is at least \(N^{1/4}\) and \(m<N\), so there are at most three factors. By (1)–(2), the one-factor and three-factor portions are nonnegative up to the same \(o(N)\) error: \(\mu(m)=-1\) and \(\log m>S\). The only adverse portion on this support is the squarefree semiprime \(m=\ell d\) with \(Q\le\ell<d\) prime. Its exact centered weight is
\[
 -\Lambda(N-\ell d)\bigl(\log(\ell d)-S\bigr)
\]
up to the total negligible model approximation. If \(\ell\) is additionally in any log interval \(\log\ell\in[A,A+\Delta]\), the absolute charge on this semiprime portion is
\[
 O\!\left(\frac{N(1+\Delta)}{L}\right)+O_\epsilon(N^{3/4+\epsilon}).
 \tag{6}
\]
To verify (6), fix \(\ell\le\sqrt N\) and apply the same argument as (5) with the variable \(h=d\) and marked \(a=\ell\). Here \(d>\ell\ge Q>D\), so the auxiliary square is one on the genuine prime \(d\), and it is also one on the retained prime \(n\). The centered weight is \(O(L^2)\). Uniformly for the interval with \(\ell\ge Q\), Chebyshev and partial summation give \(\sum_\ell1/\ell\ll(1+\Delta)/L\). Summing the floor errors over \(\ell\le\sqrt N\) gives \(N^{3/5+o(1)}\) after log weights. Thus (6) removes every \(\Delta=o(L)\) band at the same target. The broad \(\ell\) interval is still of order \(L\) in log width, and (6)'s unspecified constant does not supply a usable numerical charge for the whole row.

These results leave the broad rough-semiprime loss, the remaining \(Y<a_Q(m)<Q\) centered entries, and truncated divisor groups with \(a_Q(m)\ge Q\) unresolved. The multi-prime completed groups in (2) can be removed from the **actual** low row in (3), or treated as centered model pieces in (1). The argument is a hand proof with no new Lean or finite-target computation.
