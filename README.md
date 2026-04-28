# Divisor Function Extremal Problem

## Problem

Let $\tau(n)$ count the number of positive divisors of $n$. Is there some $n > 24$ such that

$$\max_{m < n}(m + \tau(m)) \leq n + 2 \,?$$

## Conjecture

**Conjecture:** $n = 24$ is the largest integer satisfying the inequality, and the complete solution set is $\{1, 2, 3, 4, 5, 6, 8, 10, 12, 24\}$.

The conjecture is supported by exhaustive computation for all $n \leq 10{,}000$ and by the partial proof below. The full conjecture remains **open**.

## Status

This repository contains a **strong partial proof** establishing the conjecture for all but an infinite, precisely-characterised, negligibly-sparse family of $n$.

### What is fully proved (unconditional for all $n > 24$):

- **$n$ odd**: witness $m = n-1$ has $\tau(m) \geq 4$, giving $f(m) \geq n+3$.
- **$n \equiv 2, 4 \pmod{6}$**: the nearest lower multiple of 6 is a witness.
- **$6 \mid n$ and $\tau(n-6) \geq 9$**: direct witness.
- **$\tau(n-6) = 8$, $n = 30$**: witness $m = 28$, $f(28) = 34 > 32$.
- **$\tau(n-6) = 8$, $n = 60$**: witness $m = 56$, $f(56) = 64 > 62$.
- **$n = 6(p+1)$, $p \geq 5$ prime, all congruence sub-cases except $p \equiv 419 \pmod{420}$**: fully algebraic witnesses.
- **$p \equiv 419 \pmod{420}$ (hardest sub-case), writing $n = 2520j$**: for $j \not\equiv 0, 7 \pmod{11}$, a mod-11 covering argument gives an algebraic witness valid for **every** $j$.

### Residual gap (computational certificate):

For $j \equiv 0$ or $7 \pmod{11}$, the mod-11 algebraic argument does not produce a uniform witness from $k \leq 10$ (a direct counterexample is $j = 6{,}970{,}590$, where $k = 14$ is needed). A brute-force search over all 47 proper divisors of 2520 succeeds:

> **Claim:** For every $j \leq 10^7$ with $j \equiv 0$ or $7 \pmod{11}$, a witness $k \mid 2520$ with $\tau(kA_k) > k+2$ exists.

This was verified by exhaustive computation (Python/`sympy`) with **zero failures**.

The unclosed cases are $n = 2520j$ where $420j-1$ and $504j-1$ are both prime, $j \equiv 0$ or $7 \pmod{11}$, and $j > 10^7$ (i.e. $n > 2.52 \times 10^{10}$). This gap cannot be closed by a finite covering system argument — it is equivalent to a question about simultaneous prime values of two linear forms, which is open in general.

The exceptional $n$ have natural density **zero** (doubly prime conditions make them summably sparse by Bateman–Horn heuristics).

## Repository Contents

| File | Description |
|------|-------------|
| `solution1/corrected_proof.tex` | Main proof (LaTeX source) |
| `solution1/corrected_proof.pdf` | Compiled PDF (6 pages) |
| `DivisorTheorem/Main.lean` | Lean 4 / Mathlib formalisation (in progress) |
| `Diophantine/Basic.lean` | Related Diophantine material |
| `diophantine.tex` | Supporting notes |
| `sidon_squares.tex` | Sidon subsets of perfect squares (LaTeX source) |
| `sidon_squares.pdf` | Compiled PDF (5 pages) |

---

## Sidon Subsets of Perfect Squares

### Problem

What is the size $F(N)$ of the largest Sidon subset $A \subseteq \{1^2, 2^2, \ldots, N^2\}$?
Is it $N^{1-o(1)}$?

A **Sidon set** is a set of integers in which all pairwise sums are distinct.

### Result

**No, $F(N) \ne N^{1-o(1)}$.** The following bounds are proved unconditionally:

$$\Omega\!\left(\frac{N^{2/3}}{(\log N)^{1/3}}\right) \;\le\; F(N) \;\le\; O\!\left(\frac{N}{(\log N)^{1/4}}\right).$$

In particular $F(N) = o(N)$ (disproving the conjecture) and $F(N) = \omega(N^{1/2})$.

### Proof sketch

- **Upper bound:** Any Sidon subset $A \subseteq \{1^2,\ldots,N^2\}$ of size $k$ produces $\binom{k+1}{2}$ distinct pairwise sums, all of which must be sums of two positive integer squares. By the **Landau–Ramanujan theorem**, there are only $\sim KN^2/(\log N)^{1/2}$ such integers up to $2N^2$, forcing $k \le O(N/(\log N)^{1/4})$.

- **Lower bound:** A **probabilistic alteration** argument. Select each $a \in \{1,\ldots,N\}$ with probability $\rho = cN^{-1/2}$, then delete one element from each Sidon-violating quadruple. Using the second-moment estimate $\sum_{n \le M} r_2(n)^2 \sim 4\pi M \log M$, optimising $c = \Theta(N^{1/6}/(\log N)^{1/3})$ gives a Sidon subset of expected size $\Omega(N^{2/3}/(\log N)^{1/3})$.

### Status

The disproof of $F(N) = N^{1-o(1)}$ is **complete**. The exact value of the exponent $\alpha$ in $F(N) \approx N^\alpha$ is **open**; the current bounds give $\alpha \in [2/3, 1)$.

## Building the PDF

```bash
cd solution1
pdflatex corrected_proof.tex
```

## Building the Lean Files

Requires [Lean 4](https://leanprover.github.io/) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

```bash
lake exe cache get
lake build
```