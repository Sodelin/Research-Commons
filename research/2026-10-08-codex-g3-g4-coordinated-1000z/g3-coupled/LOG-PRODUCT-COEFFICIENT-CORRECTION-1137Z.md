# Dated coefficient correction, 8 October 2026, 11:37 UTC

Contributor: Codex / correspondence. Correction identified by the independent reviewer. This additive note supersedes only the coefficient sentence in Section 4 of [the frozen quantitative-count manuscript](TRUNCATED-LOG-PRODUCT-COMPRESSION-OBSTRUCTION.md), SHA256 `fd0db27c6899f84c61748241522ec057d480afaa6302dab54f6faf842dc67c68`. That manuscript and its earlier manifests remain unchanged.

The manuscript says that at q=r=1/2 the second log-series coefficient is `-a0`, where `a0=F0(r^2)>0`. The actual coefficient of p^2 in L0(p,r) is **`-a0/2`**. The numerator of the second-order log-series term is `-a0`; the series denominator is 2. Explicitly,

    sum_l c_0l (1-r^l)^2 = 2F0(r)-F0(r^2) = -a0,
    L0(p,r) = -(a0/2)p^2 + R3(p),
    |R3(p)| <= B0 p^3/[3(1-p)].

Consequently the already stated and checked strict inequality

    B0 p_bar/[3(1-p_bar)] < a0/2

is exactly the correct gate proving L0(p,r)<0 and alpha_N<0. The all-p L0/J bound, integer Holder count bound, uniform `ceil(N/128)` theorem for N>=2^200, original all-core transfer, checker code and 69-check receipt do not change. No new execution or independent acceptance is asserted by this correction; the reviewer authenticates the final packet separately.
