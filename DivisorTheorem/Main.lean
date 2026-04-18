import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Tactic

/-!
# The unique maximizer of the divisor-shift inequality

**Theorem.** The only positive integer `n` satisfying
  `∀ m : ℕ, m < n → m + (Nat.divisors m).card ≤ n + 2`
is `n = 24`.

We write `τ(n)` for `(Nat.divisors n).card`, the number-of-divisors function.

## Proof outline

Assume `n > 24` satisfies the bound. From `m = n - 1 < n` we get `τ(n-1) ≤ 3`.
Since `n - 1 > 24`, the only possibilities are:

1. **`n - 1 = p` prime**: Then `τ(n-2) ≤ 4`. Since `n-2` is even, `> 8`, and satisfies
   a coprimality-based bound, we get `n - 2 = 2q` for a prime `q > 11`.
   Then `n - 3 = 2(q-1)`, and since `q ≥ 13`, we have `q - 1 = 2k` with `k ≥ 6`,
   giving `n - 3 = 4k` with divisors `{1, 2, 4, k, 2k, 4k}` (6 distinct values),
   so `τ(n-3) ≥ 6`. But DSB requires `τ(n-3) ≤ 5`. Contradiction.

2. **`n - 1 = p²` for prime `p`**: Then `p ≥ 5` (since `n > 24`).
   The divisors `1, 2, p-1, p+1, p²-1` of `p²-1 = n-2` are 5 distinct values,
   so `τ(n-2) ≥ 5`. But DSB requires `τ(n-2) ≤ 4`. Contradiction.

The base case `n = 24` is verified by computation: `max_{m<24}(m + τ(m)) = 26 = 24 + 2`.
-/

open Nat Finset

/-! ## Definition -/

/-- The divisor-shift-bound property. -/
def DSB (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → m + (Nat.divisors m).card ≤ n + 2

/-! ## Auxiliary: τ bounds from DSB -/

lemma tau_le_of_DSB {n k : ℕ} (hk : k < n) (h : DSB n) :
    (Nat.divisors (n - k)).card ≤ k + 2 := by
  have := h (n - k) (by omega)
  omega

/-! ## Auxiliary: τ(n) = 2 iff n is prime (for n > 1) -/

private lemma card_divisors_prime {p : ℕ} (hp : p.Prime) :
    (Nat.divisors p).card = 2 := by
  rw [hp.divisors, Finset.card_pair hp.one_lt.ne]

private lemma card_divisors_prime_sq {p : ℕ} (hp : p.Prime) :
    (Nat.divisors (p ^ 2)).card = 3 := by
  rw [Nat.Prime.divisors_sq hp]
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  have h1sq : (1 : ℕ) ≠ p ^ 2 := by positivity
  have hpsq : p ≠ p ^ 2 := by nlinarith [hp.one_lt]
  rw [show ({p ^ 2, p, 1} : Finset ℕ) = ({p ^ 2, p} : Finset ℕ) ∪ {1} from by
    ext; simp [or_comm, or_assoc]]
  rw [Finset.card_union_of_disjoint (by simp [hpsq.symm, h1sq.symm])]
  rw [Finset.card_pair hpsq, Finset.card_singleton]

/-! ## Key Lemma 1: p ≥ 5 prime → τ(p² - 1) ≥ 5 -/

lemma tau_pred_sq_ge5 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    5 ≤ (Nat.divisors (p ^ 2 - 1)).card := by
  have hpsq : p ^ 2 ≥ 25 := by nlinarith
  have hm_ne0 : p ^ 2 - 1 ≠ 0 := by omega
  -- p is odd
  have hpodd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr (by omega)
  -- p² - 1 = (p-1)(p+1)
  have hfact : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp.pos
    nlinarith [Nat.sub_add_cancel h1]
  -- Witness divisors: 1, 2, p-1, p+1, p²-1
  have hd1 : (1 : ℕ) ∣ p ^ 2 - 1 := one_dvd _
  have hdpm1 : p - 1 ∣ p ^ 2 - 1 := ⟨p + 1, hfact.symm⟩
  have hdpp1 : p + 1 ∣ p ^ 2 - 1 := ⟨p - 1, by linarith [hfact]⟩
  have hd2 : (2 : ℕ) ∣ p ^ 2 - 1 := (show (2 : ℕ) ∣ p - 1 by omega).trans hdpm1
  have hdself : p ^ 2 - 1 ∣ p ^ 2 - 1 := dvd_refl _
  -- Build 5-element subfinset
  have hS_sub : ({1, 2, p - 1, p + 1, p ^ 2 - 1} : Finset ℕ) ⊆ Nat.divisors (p ^ 2 - 1) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    simp only [Nat.mem_divisors, hm_ne0, and_true]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hd1; · exact hd2; · exact hdpm1; · exact hdpp1; · exact hdself
  -- Card = 5 (values distinct when p ≥ 5)
  have hS_card : ({1, 2, p - 1, p + 1, p ^ 2 - 1} : Finset ℕ).card = 5 := by
    -- p^2 - 1 + 1 = p^2 (used to reason about ℕ subtraction)
    have hback : p ^ 2 - 1 + 1 = p ^ 2 := by omega
    have h1 : (1 : ℕ) ∉ ({2, p - 1, p + 1, p ^ 2 - 1} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]; omega
    have h2 : (2 : ℕ) ∉ ({p - 1, p + 1, p ^ 2 - 1} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]; omega
    have h3 : p - 1 ∉ ({p + 1, p ^ 2 - 1} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]; push_not
      exact ⟨by omega, fun h => by nlinarith [hback]⟩
    have h4 : p + 1 ∉ ({p ^ 2 - 1} : Finset ℕ) := by
      simp only [mem_singleton]; intro h; nlinarith [hback]
    simp only [card_insert_of_notMem h1, card_insert_of_notMem h2,
      card_insert_of_notMem h3, card_insert_of_notMem h4, card_singleton]
  linarith [Finset.card_le_card hS_sub]

/-! ## Key Lemma 2: n even, n > 8, τ(n) ≤ 4 → n = 2p for prime p -/

lemma two_prime_of_even_small_tau {n : ℕ} (hn8 : 8 < n) (heven : 2 ∣ n)
    (htau : (Nat.divisors n).card ≤ 4) :
    ∃ p : ℕ, p.Prime ∧ n = 2 * p := by
  obtain ⟨m, hm⟩ := heven
  subst hm
  rename_i m
  -- Two cases: m odd or m even
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- m even: n = 2*m = 4*k, so n = 4k
    -- Exhibit 5 divisors: 1, 2, 4, k, n
    exfalso
    have hk3 : 3 ≤ k := by omega
    have hn_eq : 2 * m = 4 * k := by omega
    have hn0 : 2 * m ≠ 0 := by omega
    have hd1 : (1 : ℕ) ∣ 2 * m := one_dvd _
    have hd2 : (2 : ℕ) ∣ 2 * m := ⟨m, rfl⟩
    have hd4 : (4 : ℕ) ∣ 2 * m := ⟨k, by omega⟩
    have hdk : k ∣ 2 * m := ⟨4, by omega⟩
    have hdself : 2 * m ∣ 2 * m := dvd_refl _
    have hS_sub : ({1, 2, 4, k, 2 * m} : Finset ℕ) ⊆ Nat.divisors (2 * m) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      simp only [Nat.mem_divisors, hn0, and_true]
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact hd1; · exact hd2; · exact hd4; · exact hdk; · exact hdself
    have hS_card : ({1, 2, 4, k, 2 * m} : Finset ℕ).card = 5 := by
      have hmem1 : (1 : ℕ) ∉ ({2, 4, k, 2 * m} : Finset ℕ) := by simp; omega
      have hmem2 : (2 : ℕ) ∉ ({4, k, 2 * m} : Finset ℕ) := by simp; omega
      have hmem4 : (4 : ℕ) ∉ ({k, 2 * m} : Finset ℕ) := by simp; omega
      have hmemk : k ∉ ({2 * m} : Finset ℕ) := by simp; omega
      simp only [card_insert_of_notMem hmem1, card_insert_of_notMem hmem2,
        card_insert_of_notMem hmem4, card_insert_of_notMem hmemk, card_singleton]
    linarith [Finset.card_le_card hS_sub]
  · -- m odd: n = 2m, m odd, m > 4
    have hm_gt4 : 4 < m := by omega
    have hm_ne0 : m ≠ 0 := by omega
    have hm_odd_bit : m % 2 = 1 := by omega
    have hm_odd : ¬ 2 ∣ m := by omega
    have hcop : Nat.Coprime 2 m := by
      rw [Nat.coprime_two_left, Nat.odd_iff]; exact hm_odd_bit
    -- τ(2m) = τ(2) * τ(m) = 2 * τ(m)
    have htau_eq : 2 * (Nat.divisors m).card = (Nat.divisors (2 * m)).card := by
      rw [Nat.Coprime.card_divisors_mul hcop]
      norm_num [card_divisors_prime (by norm_num : Nat.Prime 2)]
    -- τ(m) ≤ 2
    have htm_le2 : (Nat.divisors m).card ≤ 2 := by linarith
    -- τ(m) ≥ 2 (m > 1)
    have hm_gt1 : 1 < m := by omega
    have h1_mem : (1 : ℕ) ∈ Nat.divisors m := by simp [hm_ne0]
    have hm_mem : m ∈ Nat.divisors m := Nat.mem_divisors_self m hm_ne0
    have htm_ge2 : 2 ≤ (Nat.divisors m).card :=
      Finset.one_lt_card.mpr ⟨1, h1_mem, m, hm_mem, hm_gt1.ne⟩
    -- τ(m) = 2, so m is prime
    have htm2 : (Nat.divisors m).card = 2 := le_antisymm htm_le2 htm_ge2
    -- m's divisors are exactly {1, m}
    have hdivs_eq : Nat.divisors m = {1, m} := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [mem_insert, mem_singleton]
        by_contra hne
        push_not at hne
        -- x is a divisor of m, not 1 or m. That gives 3 distinct divisors.
        have h3 : ({1, x, m} : Finset ℕ).card ≤ (Nat.divisors m).card := by
          apply Finset.card_le_card
          intro y hy
          simp only [mem_insert, mem_singleton] at hy
          simp only [Nat.mem_divisors, hm_ne0, and_true]
          rcases hy with rfl | rfl | rfl
          · exact one_dvd _
          · exact (Nat.dvd_of_mem_divisors hx)
          · exact dvd_refl m
        have h1xm : ({1, x, m} : Finset ℕ).card = 3 := by
          have hmem1 : (1 : ℕ) ∉ ({x, m} : Finset ℕ) := by simp; exact ⟨hne.1, hm_gt1.ne⟩
          have hmemx : x ∉ ({m} : Finset ℕ) := by simp; exact hne.2
          simp only [card_insert_of_notMem hmem1, card_insert_of_notMem hmemx, card_singleton]
        linarith
      · simp [htm2, Finset.card_pair hm_gt1.ne]
    -- m is prime iff its only divisors are 1 and m
    refine ⟨m, ?_, rfl⟩
    rwa [Nat.prime_def_lt_prime]
    constructor
    · omega
    · intro k hk1 hkm hklt
      have hk_in : k ∈ Nat.divisors m := by simp [Nat.mem_divisors, hm_ne0, hkm]
      rw [hdivs_eq] at hk_in
      simp at hk_in
      omega

/-! ## Key Lemma 3: q prime, q > 11 → τ(2*(q-1)) ≥ 6 -/

lemma tau_twice_pred_ge6 {q : ℕ} (hq : q.Prime) (hq11 : 11 < q) :
    6 ≤ (Nat.divisors (2 * (q - 1))).card := by
  -- q is an odd prime ≥ 13
  have hq_ge13 : 13 ≤ q := by
    rcases hq.eq_two_or_odd with rfl | ⟨r, hr⟩
    · omega
    · have := hq.two_le; omega
  have hq_odd : q % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two hq).mpr (by omega)
  -- q - 1 is even; write q - 1 = 2 * k with k ≥ 6
  have hq1_even : 2 ∣ q - 1 := by omega
  obtain ⟨k, hk⟩ : ∃ k, q - 1 = 2 * k := hq1_even
  have hk_ge6 : 6 ≤ k := by omega
  -- 2*(q-1) = 4*k; exhibit 6 divisors: 1, 2, 4, k, 2k, 4k
  have hne0 : 2 * (q - 1) ≠ 0 := by omega
  have hval : 2 * (q - 1) = 4 * k := by omega
  have hd1 : (1 : ℕ) ∣ 4 * k := one_dvd _
  have hd2 : (2 : ℕ) ∣ 4 * k := ⟨2 * k, by ring⟩
  have hd4 : (4 : ℕ) ∣ 4 * k := ⟨k, by ring⟩
  have hdk : k ∣ 4 * k := ⟨4, by ring⟩
  have hd2k : 2 * k ∣ 4 * k := ⟨2, by ring⟩
  have hdself : 4 * k ∣ 4 * k := dvd_refl _
  have hS_sub : ({1, 2, 4, k, 2 * k, 4 * k} : Finset ℕ) ⊆ Nat.divisors (2 * (q - 1)) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [hval]
    simp only [Nat.mem_divisors, show 4 * k ≠ 0 from by omega, and_true]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hd1; · exact hd2; · exact hd4; · exact hdk; · exact hd2k; · exact hdself
  have hS_card : ({1, 2, 4, k, 2 * k, 4 * k} : Finset ℕ).card = 6 := by
    have hmem1 : (1 : ℕ) ∉ ({2, 4, k, 2 * k, 4 * k} : Finset ℕ) := by simp; omega
    have hmem2 : (2 : ℕ) ∉ ({4, k, 2 * k, 4 * k} : Finset ℕ) := by simp; omega
    have hmem4 : (4 : ℕ) ∉ ({k, 2 * k, 4 * k} : Finset ℕ) := by simp; omega
    have hmemk : k ∉ ({2 * k, 4 * k} : Finset ℕ) := by simp; omega
    have hmem2k : 2 * k ∉ ({4 * k} : Finset ℕ) := by simp; omega
    simp only [card_insert_of_notMem hmem1, card_insert_of_notMem hmem2,
      card_insert_of_notMem hmem4, card_insert_of_notMem hmemk,
      card_insert_of_notMem hmem2k, card_singleton]
  linarith [Finset.card_le_card hS_sub]

/-! ## Main: no DSB above 24 -/

/-- For all `n > 24`, `DSB n` fails. -/
theorem no_DSB_above_24 (n : ℕ) (hn : 24 < n) : ¬ DSB n := by
  intro h
  -- τ(n-1) ≤ 3 (from m = n-1)
  have htau1 : (Nat.divisors (n - 1)).card ≤ 3 :=
    tau_le_of_DSB (by omega) h |>.trans_eq (by omega) |>.trans (le_refl 3)
  -- n - 1 > 1
  have hn1_gt1 : 1 < n - 1 := by omega
  have hn1_ne0 : n - 1 ≠ 0 := by omega
  -- Case 1: n-1 prime. Case 2: n-1 = p² for some prime p.
  -- These are the only cases when τ(n-1) ≤ 3 and n-1 > 1 (since τ ≥ 2 for n-1 prime-or-composite).
  -- We prove this: τ(n-1) ≤ 3 and n-1 > 1 → n-1 prime or n-1 = p^2.
  -- Proof: τ(n-1) ≥ 2 (has divisors 1 and n-1). If τ = 2: prime. If τ = 3:
  --   n-1 composite → has a prime factor p with 1 < p < n-1.
  --   Divisors include 1, p, n-1 (distinct since 1 < p < n-1).
  --   If any other divisor q exists: τ ≥ 4. So exactly {1, p, n-1}.
  --   This means (n-1)/p has no proper divisors other than 1, so (n-1)/p = p (prime factor).
  --   Hence n-1 = p^2.
  -- Let's just prove the key cases by case analysis on whether n-1 is prime.
  by_cases hprime : (n - 1).Prime
  · -- Case 1: n-1 prime
    have hn1_prime := hprime
    -- τ(n-2) ≤ 4
    have htau2 : (Nat.divisors (n - 2)).card ≤ 4 := by
      have := tau_le_of_DSB (by omega) h; omega
    -- n-2 is even (n-1 is odd prime > 2, so n-1 is odd, so n is even, so n-2 is even)
    have hn1_odd : (n - 1) % 2 = 1 :=
      (Nat.Prime.mod_two_eq_one_iff_ne_two hn1_prime).mpr (by omega)
    have hn2_even : 2 ∣ n - 2 := by omega
    -- n-2 > 8 (since n > 24)
    have hn2_gt8 : 8 < n - 2 := by omega
    -- By two_prime_of_even_small_tau: n-2 = 2q for prime q
    obtain ⟨q, hq_prime, hn2_eq⟩ := two_prime_of_even_small_tau hn2_gt8 hn2_even htau2
    -- q > 11 (since n-2 > 22)
    have hq_gt11 : 11 < q := by linarith [show n - 2 = 2 * q from hn2_eq]
    -- n-3 = 2*(q-1)
    have hn3_eq : n - 3 = 2 * (q - 1) := by omega
    -- τ(n-3) ≥ 6
    have htau3_big : 6 ≤ (Nat.divisors (n - 3)).card := by
      rw [hn3_eq]; exact tau_twice_pred_ge6 hq_prime hq_gt11
    -- DSB gives τ(n-3) ≤ 5
    have htau3 : (Nat.divisors (n - 3)).card ≤ 5 := by
      have := tau_le_of_DSB (by omega) h; omega
    linarith
  · -- Case 2: n-1 is not prime
    -- We show n-1 = p^2 for some prime p, hence τ = 3.
    -- First: τ(n-1) ≥ 2 (n-1 > 1)
    have htau1_ge2 : 2 ≤ (Nat.divisors (n - 1)).card := by
      have := Finset.one_lt_card.mpr
        ⟨1, by simp [hn1_ne0], n-1, Nat.mem_divisors_self _ hn1_ne0,
          hn1_gt1.ne⟩
      exact this
    -- τ(n-1) ∈ {2, 3}. It's 3 (since it's not prime, ruling out 2).
    have htau1_eq3 : (Nat.divisors (n - 1)).card = 3 := by
      have : (Nat.divisors (n - 1)).card = 2 ↔ (n - 1).Prime := by
        constructor
        · intro h2
          rw [Nat.prime_def_lt_prime]
          constructor
          · omega
          · intro k hk1 hkdvd hklt
            have hk_in : k ∈ Nat.divisors (n - 1) := by
              simp [Nat.mem_divisors, hn1_ne0, hkdvd]
            -- k ≠ 1 and k ≠ n-1 (since k < n-1), so card ≥ 3
            have : ({1, k, n - 1} : Finset ℕ).card ≤ (Nat.divisors (n - 1)).card := by
              apply Finset.card_le_card
              intro y hy
              simp only [mem_insert, mem_singleton] at hy
              rcases hy with rfl | rfl | rfl
              · simp [hn1_ne0]
              · exact hk_in
              · exact Nat.mem_divisors_self _ hn1_ne0
            have h3 : ({1, k, n - 1} : Finset ℕ).card = 3 := by
              have hmem1 : (1 : ℕ) ∉ ({k, n - 1} : Finset ℕ) := by simp; omega
              have hmemk : k ∉ ({n - 1} : Finset ℕ) := by simp; omega
              simp only [card_insert_of_notMem hmem1, card_insert_of_notMem hmemk, card_singleton]
            linarith
        · intro hpr
          rw [card_divisors_prime hpr]
      linarith [this.mpr.mt hprime, htau1_ge2]
    -- n-1 has exactly 3 divisors: 1, p, n-1 for some prime p with p^2 = n-1
    -- Get the prime factor of n-1
    obtain ⟨p, hp, hpdvd⟩ := (n - 1).exists_prime_and_dvd (by omega)
    -- n-1 = p * q for some q. Since τ(n-1) = 3 and there are exactly 3 divisors {1, p, n-1},
    -- we need p = q, i.e., n-1 = p^2.
    -- Proof: the divisors 1, p, and (n-1)/p all divide n-1 and are ≤ n-1.
    -- If (n-1)/p ≠ p, then (n-1)/p is a distinct divisor from {1, p, n-1}... unless (n-1)/p = n-1 (impossible since p > 1) or (n-1)/p = 1 (then n-1 = p, but n-1 > p^... wait).
    -- Actually let q = (n-1)/p. The divisors of n-1 include 1, p, q, n-1.
    -- If these are all distinct (i.e., q ≠ 1, q ≠ p, q ≠ n-1), then τ ≥ 4. Contradiction.
    -- q ≠ n-1: since p > 1, q = (n-1)/p < n-1.
    -- q ≠ 1: since q = (n-1)/p and n-1 > p (n-1 not prime means composite, so n-1 ≥ p^2 ≥ p*2), so q ≥ 2.
    -- WAIT: n-1 not prime doesn't mean n-1 ≥ p^2. It means n-1 = p*q with q > 1.
    -- Actually: n-1 not prime and n-1 > 1 means n-1 is composite (since n-1 > 1).
    -- So n-1 = p * q where q = (n-1)/p, and p ≤ q (take p = minFac(n-1)).
    -- If p < q: divisors 1, p, q, n-1 are 4 distinct values (1 < p < q < n-1). τ ≥ 4. Contradiction.
    -- If p = q: n-1 = p^2. ✓
    obtain ⟨q', hq'⟩ := hpdvd
    -- q' = (n-1)/p
    -- Cases: p = q' or p ≠ q'
    by_cases hpq : p = q'
    · -- n-1 = p^2
      subst hpq
      have hn1_psq : n - 1 = p ^ 2 := by ring_nf; linarith [hq']
      -- τ(n-2) = τ(p^2 - 1) ≥ 5
      have hp5 : 5 ≤ p := by
        have : 24 < p ^ 2 := by omega
        -- p^2 > 24 → p ≥ 5 (since 4^2 = 16 ≤ 24)
        by_contra hlt
        push_not at hlt
        interval_cases p <;> simp_all [Nat.Prime] <;> omega
      have hn2_eq : n - 2 = p ^ 2 - 1 := by omega
      have htau2_big : 5 ≤ (Nat.divisors (n - 2)).card := by
        rw [hn2_eq]; exact tau_pred_sq_ge5 hp hp5
      have htau2 : (Nat.divisors (n - 2)).card ≤ 4 := by
        have := tau_le_of_DSB (by omega) h; omega
      linarith
    · -- n-1 = p*q' with p ≠ q'. If additionally p < q' (which happens when p = minFac):
      -- divisors 1, p, q', n-1 are 4 distinct. τ ≥ 4.
      exfalso
      -- We need p ≠ 1 (true since p prime) and p < q' (or q' < p).
      -- Either way 1, p, q', p*q' are all divisors and we need them distinct.
      have hp1 : p ≠ 1 := hp.one_lt.ne'
      have hq1 : q' ≠ 1 := by
        intro hq1; rw [hq1, mul_one] at hq'
        exact hprime (hq' ▸ hp)
      have hpq'n : p ≠ n - 1 := by
        intro heq; rw [← heq] at hq'
        have : q' = 1 := Nat.eq_one_of_mul_eq_one_right hq' |>.symm
          -- p * q' = p means q' = 1
        simp [← heq, hp.one_lt.ne] at hq'
        exact hq1 (Nat.eq_one_of_pos_of_self_mul_self_eq_one hq'.symm |>.symm)
      have hq'n : q' ≠ n - 1 := by
        intro heq; rw [← heq] at hq'
        exact hp1 (Nat.eq_one_of_self_mul_self_eq_self (by linarith [hq']))
      -- Actually simpler: p < n-1 (since q' > 1 and n-1 = p*q') and q' < n-1 similarly.
      have hp_lt : p < n - 1 := by
        calc p < p * q' := Nat.lt_mul_of_lt_one hp.pos (by omega)
          _ = n - 1 := hq'.symm
      have hq'_lt : q' < n - 1 := by
        calc q' < p * q' := Nat.lt_mul_of_lt_one (by omega) hp.one_lt
          _ = n - 1 := hq'.symm
      -- Four distinct divisors of n-1: 1, p, q', n-1
      have h4div : ({1, p, q', n - 1} : Finset ℕ) ⊆ Nat.divisors (n - 1) := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        simp only [Nat.mem_divisors, hn1_ne0, and_true]
        rcases hx with rfl | rfl | rfl | rfl
        · exact one_dvd _
        · exact ⟨q', hq'.symm⟩
        · exact ⟨p, by linarith [hq']⟩
        · exact dvd_refl _
      have h4card : ({1, p, q', n - 1} : Finset ℕ).card = 4 := by
        have hmem1 : (1 : ℕ) ∉ ({p, q', n - 1} : Finset ℕ) := by
          simp; exact ⟨hp.one_lt.ne, by omega, hn1_gt1.ne⟩
        have hmemp : p ∉ ({q', n - 1} : Finset ℕ) := by
          simp; exact ⟨hpq, hp_lt.ne⟩
        have hmemq' : q' ∉ ({n - 1} : Finset ℕ) := by simp; exact hq'_lt.ne
        simp only [card_insert_of_notMem hmem1, card_insert_of_notMem hmemp,
          card_insert_of_notMem hmemq', card_singleton]
      linarith [Finset.card_le_card h4div, htau1_eq3]

/-! ## Base case: n = 24 satisfies DSB -/

theorem dsb_24 : DSB 24 := by
  intro m hm
  interval_cases m <;> simp_all [Nat.divisors] <;> decide

/-! ## Main theorem -/

/-- The unique positive integer satisfying DSB is n = 24. -/
theorem unique_DSB : ∀ n : ℕ, 1 ≤ n → (DSB n ↔ n = 24) := by
  intro n _
  constructor
  · intro hDSB
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · -- n < 24: show DSB fails by exhibiting m with m + τ(m) > n + 2
      -- We check all n ∈ {1,..,23} via decide
      interval_cases n
      all_goals (simp only [DSB] at hDSB;
                 first
                 | (have := hDSB 1 (by norm_num); simp at this)
                 | (have := hDSB 2 (by norm_num); norm_num [Nat.divisors] at this)
                 | exact absurd rfl (by
                     intro h
                     simp [DSB, Nat.divisors] at hDSB))
    · exact no_DSB_above_24 n hgt hDSB
  · rintro rfl; exact dsb_24
