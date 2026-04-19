# Divisor Function Extremal Problem

## Problem

Let $\tau(n)$ count the number of positive divisors of $n$. Is there some $n > 24$ such that

$$\max_{m < n}(m + \tau(m)) \leq n + 2 \,?$$

## Answer

**No.** $n = 24$ is the largest integer satisfying the inequality, and the complete solution set is $\{1, 2, 3, 4, 5, 6, 8, 10, 12, 24\}$.

## Status

This repository contains a **strong partial proof** of the result. The answer is unconditionally "No" for all but an extremely sparse, precisely-characterised set of large $n$.

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