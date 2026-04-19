import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.Group.Int.Units

/-!
# No integer solutions to 6 + x³ + x·y²·z + z² = 0
-/

theorem no_integer_solutions : ∀ x y z : ℤ, 6 + x ^ 3 + x * y ^ 2 * z + z ^ 2 ≠ 0 := by
  intro x y z h0
  have heq0 : x ^ 3 + x * y ^ 2 * z + z ^ 2 + 6 = 0 := by linarith

  -- Step 1: x is odd
  have hx_odd : ¬ (2 : ℤ) ∣ x := by
    intro ⟨k, hk⟩; subst hk
    have hz2 : (2 : ℤ) ∣ z := by
      by_contra hze
      obtain ⟨q, hq⟩ : (2 : ℤ) ∣ (2 * k) ^ 3 + (2 * k) * y ^ 2 * z :=
        ⟨4 * k ^ 3 + k * y ^ 2 * z, by ring⟩
      have hz2sq : z ^ 2 = 2 * (-q - 3) := by linarith
      have : z % 2 = 0 := by
        rcases Int.even_or_odd z with ⟨n, hn⟩ | ⟨n, hn⟩
        · rw [hn]; omega
        · exfalso; rw [hn] at hz2sq
          have hexp : (2 * n + 1) ^ 2 = 4 * n ^ 2 + 4 * n + 1 := by ring
          have heven : 2 ∣ 4 * n ^ 2 + 4 * n := ⟨2 * n ^ 2 + 2 * n, by ring⟩
          omega
      exact hze ⟨z / 2, by omega⟩
    obtain ⟨m, hm⟩ := hz2; subst hm
    obtain ⟨q, hq⟩ : (4 : ℤ) ∣ (2 * k) ^ 3 + (2 * k) * y ^ 2 * (2 * m) + (2 * m) ^ 2 :=
      ⟨2 * k ^ 3 + k * m * y ^ 2 + m ^ 2, by ring⟩
    have heq_km : (2 * k) ^ 3 + 2 * k * y ^ 2 * (2 * m) + (2 * m) ^ 2 + 6 = 0 := heq0
    have hq' : (2 * k) ^ 3 + 2 * k * y ^ 2 * (2 * m) + (2 * m) ^ 2 = 4 * q := by
      linarith [show (2 * k) ^ 3 + (2 * k) * y ^ 2 * (2 * m) + (2 * m) ^ 2 =
        (2 * k) ^ 3 + 2 * k * y ^ 2 * (2 * m) + (2 * m) ^ 2 from by ring]
    have : 4 * q + 6 = 0 := by linarith [hq', heq_km]
    omega

  -- Step 2: z is odd
  have hz_odd : ¬ (2 : ℤ) ∣ z := by
    intro ⟨m, hm⟩; subst hm
    have h2x3 : (2 : ℤ) ∣ x ^ 3 := by
      exact ⟨-(x * y ^ 2 * m + 2 * m ^ 2 + 3), by linarith⟩
    exact hx_odd ((show Prime (2 : ℤ) by decide).dvd_of_dvd_pow h2x3)

  -- Step 3: 3 ∤ x
  have hx_mod3 : ¬ (3 : ℤ) ∣ x := by
    intro ⟨a, ha⟩; subst ha
    have hz3sq : (3 : ℤ) ∣ z ^ 2 := by
      refine ⟨-(9 * a ^ 3 + a * y ^ 2 * z + 2), ?_⟩
      have heq3 : (3 * a) ^ 3 + 3 * a * y ^ 2 * z + z ^ 2 + 6 = 0 := heq0
      linarith
    have hz3 : (3 : ℤ) ∣ z := (show Prime (3 : ℤ) by decide).dvd_of_dvd_pow hz3sq
    obtain ⟨b, hb⟩ := hz3; subst hb
    obtain ⟨q, hq⟩ : (9 : ℤ) ∣ (3 * a) ^ 3 + (3 * a) * y ^ 2 * (3 * b) + (3 * b) ^ 2 :=
      ⟨3 * a ^ 3 + a * y ^ 2 * b + b ^ 2, by ring⟩
    have heq9 : (3 * a) ^ 3 + 3 * a * y ^ 2 * (3 * b) + (3 * b) ^ 2 + 6 = 0 := heq0
    have hq' : (3 * a) ^ 3 + 3 * a * y ^ 2 * (3 * b) + (3 * b) ^ 2 = 9 * q := by
      linarith [show (3 * a) ^ 3 + (3 * a) * y ^ 2 * (3 * b) + (3 * b) ^ 2 =
        (3 * a) ^ 3 + 3 * a * y ^ 2 * (3 * b) + (3 * b) ^ 2 from by ring]
    have : 9 * q + 6 = 0 := by linarith [hq', heq9]
    omega

  -- Step 4: gcd(x, z) = 1
  have hcop : IsCoprime x z := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hdx : (Int.gcd x z : ℤ) ∣ x := Int.gcd_dvd_left x z
    have hdz : (Int.gcd x z : ℤ) ∣ z := Int.gcd_dvd_right x z
    have hd6 : (Int.gcd x z : ℤ) ∣ 6 := by
      have h1 := hdx.pow (n := 3) (by norm_num)
      have h2 := (hdx.mul_right (y ^ 2)).mul_right z
      have h3 := hdz.pow (n := 2) (by norm_num)
      have hzero := dvd_add (dvd_add h1 h2) h3
      rw [show x ^ 3 + x * y ^ 2 * z + z ^ 2 = -6 from by linarith] at hzero
      exact dvd_neg.mp hzero
    have hd6n : Int.gcd x z ∣ 6 := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr hd6
    have hd_odd : ¬ (2 : ℕ) ∣ Int.gcd x z := by
      intro h2
      exact hx_odd ((show (2 : ℤ) ∣ (Int.gcd x z : ℤ) by exact_mod_cast h2).trans hdx)
    have hd3 : ¬ (3 : ℕ) ∣ Int.gcd x z := by
      intro h3
      exact hx_mod3 ((show (3 : ℤ) ∣ (Int.gcd x z : ℤ) by exact_mod_cast h3).trans hdx)
    have hdivs6 : ∀ n : ℕ, n ∣ 6 → ¬ 2 ∣ n → ¬ 3 ∣ n → n = 1 := by
      intro n hn hn2 hn3
      have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) hn
      interval_cases n <;> omega
    exact hdivs6 _ hd6n hd_odd hd3

  -- Step 5: z | 6 (hence z = ±1 or z = ±3, since z is odd)
  -- From heq0: z | x^3 + 6. Since gcd(z,x)=1, z | 6.
  have hzdvd6 : z ∣ 6 := by
    have hzx3p6 : z ∣ x ^ 3 + 6 := by
      have h1 : z ∣ x * y ^ 2 * z := dvd_mul_left z _
      have h2 : z ∣ z ^ 2 := dvd_pow_self z (by norm_num)
      have hzero : z ∣ x ^ 3 + x * y ^ 2 * z + z ^ 2 + 6 := by
        rw [show x ^ 3 + x * y ^ 2 * z + z ^ 2 + 6 = 0 from heq0]
        exact dvd_zero z
      have hsum : z ∣ x ^ 3 + 6 := by
        have := dvd_sub hzero (dvd_add h1 h2)
        simp only [show x ^ 3 + x * y ^ 2 * z + z ^ 2 + 6 - (x * y ^ 2 * z + z ^ 2) =
          x ^ 3 + 6 from by ring] at this
        exact this
      exact hsum
    -- gcd(z, x^3) = 1 since gcd(z,x)=1
    have hcop_zx3 : IsCoprime z (x ^ 3) := hcop.symm.pow_right
    -- z | x^3 + 6 and z | x^3 (if z were coprime to x^3 this already gives z|6)
    -- Actually: z | (x^3+6) - x^3 = 6 iff z | x^3 which doesn't hold in general.
    -- Correct: z | x^3+6 and IsCoprime z x^3 → consider z | (x^3+6) - x^3*(something).
    -- Better: from IsCoprime z x^3, ∃ a b, a*z + b*(x^3) = 1.
    -- Then 6 = 6*(a*z + b*x^3) = 6*a*z + b*6 = 6*a*z + b*(x^3+6 - x^3)
    --       = 6*a*z + b*(x^3+6) - b*x^3.
    -- z | 6*a*z and z | b*(x^3+6). So z | 6. But we need to also show z | b*x^3... hmm.
    -- Actual clean argument: From IsCoprime z x^3:
    --   IsCoprime.dvd_of_dvd_mul_right : IsCoprime k n → k ∣ m * n → k ∣ m
    -- z | (x^3+6) and z | x^3+6. We want z | 6.
    -- From IsCoprime z x^3 and z | x^3+6: z | (x^3+6) - x^3 iff z | x^3.
    -- But z ∤ x^3 in general!
    -- Use: z | x^3+6. And from IsCoprime z x^3: gcd(z, x^3)=1.
    -- Now: gcd(z, x^3+6) could be > 1. So IsCoprime z (x^3+6) is NOT what we have.
    -- What we DO have: z | x^3+6 (established). And IsCoprime z x^3.
    -- From IsCoprime z x^3: ∃ u v, u*z + v*(x^3) = 1.
    -- 6 = 6*u*z + 6*v*x^3 = 6*u*z + v*(6*x^3).
    -- And x^3+6 = z*c (some c, since z | x^3+6).
    -- 6*v*x^3 = v*(z*c - 6) = v*z*c - 6v.
    -- 6 = 6*u*z + v*z*c - 6v = z*(6u+vc) - 6v.
    -- z*(6u+vc) = 6 + 6v = 6*(1+v).
    -- So z | 6*(1+v). Hmm, depends on v.
    -- CORRECT APPROACH: From IsCoprime z (x^3):
    --   use IsCoprime.dvd_of_dvd_mul_right : IsCoprime z x^3 → z ∣ 6*x^3 → z ∣ 6.
    -- z | 6*x^3: z | x^3+6 and z | x^3+6, not directly 6*x^3.
    -- z | 6*x^3 := 6*(x^3+6) - 6*6 = ... not useful.
    -- Actually: z | 6*(x^3+6) (trivially). And 6*(x^3+6) = 6*x^3 + 36.
    -- So z | 6*x^3 + 36. And if z | 6*x^3 then z | 36.
    -- Hmm not clean. Different approach:
    -- z | x^3+6 and z | z*(x^3+6) (trivially). And want z | 6.
    -- Consider: IsCoprime z x^3 means ∃ u v, u*z + v*x^3 = 1.
    -- Multiply by 6: 6*u*z + 6*v*x^3 = 6. So 6*v*x^3 ≡ 6 (mod z).
    -- And v*x^3 ≡ 1-u*z ≡ 1 (mod z, since u*z ≡ 0). So v*x^3 ≡ 1 (mod z).
    -- Hmm: 6 ≡ 6*v*x^3 ... only if v*x^3 ≡ 1 (mod z). And 6*v*x^3 ≡ 6 (mod z). AND:
    -- x^3 ≡ -6 (mod z) (from z | x^3+6). So v*x^3 ≡ -6*v (mod z). ≡ 1 (mod z).
    -- So -6*v ≡ 1 (mod z) → 6*v ≡ -1 (mod z) → 6*(6v) ≡ -6 (mod z) → 36v ≡ -6 ≡ x^3 (mod z).
    -- Hmm, circular.
    -- CORRECT SHORT PROOF: from z | x^3+6 and IsCoprime z x^3:
    --   Write 6 = (x^3+6) - x^3. Then z ∣ (x^3+6) and (from Bezout) x^3 = (1 - u*z)/v for...
    -- NO: z | (x^3+6) and we want z | 6, which is (x^3+6) - x^3.
    -- z | (x^3+6) - x^3 iff z | x^3 iff (since IsCoprime z x^3) z | 1 iff IsUnit z.
    -- So: z | 6 iff IsUnit z! And IsUnit z iff z = ±1 (odd divisor of 6 = ±1 in ℤ).
    -- So z | 6 does NOT follow from what we have unless we already know IsUnit z!
    -- WE'RE BACK TO SQUARE ONE.
    --
    -- WAIT. The correct argument IS:
    -- z | x^3+6. Let's factor this differently. NOT z | 6 directly.
    -- Instead: gcd(z, x) = 1 and x^3 ≡ -6 (mod z).
    -- We need to derive a contradiction WITHOUT first knowing IsUnit z.
    --
    -- THE REAL KEY INSIGHT: z | x^3+6 and x | z^2+6.
    -- From x | z^2+6 and z | x^3+6 and both x,z odd, gcd=1:
    -- Need both to hold simultaneously, but the original equation forces this to be impossible
    -- unless (x,z) = (±1, ±1) etc.
    --
    -- Wait — actually WE DON'T NEED "z | 6" directly.
    -- The complete proof can proceed as follows:
    -- Use z | x^3 + 6. And gcd(z,x)=1.
    -- Since gcd(z,x^3)=1 (from gcd(z,x)=1), Bezout gives ∃ u v, u*z + v*(x^3) = 1.
    -- → v*(x^3) ≡ 1 (mod z). And x^3 ≡ -6 (mod z). So v*(-6) ≡ 1 (mod z). So z | 6v+1.
    -- And from u*z + v*x^3 = 1: 6u*z + 6v*x^3 = 6.
    -- z | x^3+6 → z*c = x^3+6. 6v*x^3 = 6v*(z*c - 6) = 6vzc - 36v.
    -- 6u*z + 6vzc - 36v = 6. z*(6u+6vc) = 6+36v. z | 6+36v = 6*(1+6v).
    -- From z | 6v+1 (established above): z | 6*(6v+1) = 36v+6. YES SAME as 6+36v. Trivially z | it.
    -- So z | 6*(6v+1) and from gcd(z,6) = ? We need gcd(z,6)=1 (z odd AND 3∤z?).
    -- But we haven't shown 3∤z!
    -- If gcd(z,6) = 1: z | 1+6v. And from z*(6u+6vc) = 6*(1+6v): z | 6*(1+6v)/1 = 6*(1+6v).
    -- If gcd(z,6)=1 and z | 6*(1+6v): z | 1+6v. Then z | 6v+1 (same as 1+6v). Also: z | u*z+v*x^3=1 → z | v*x^3-1...
    -- Hmm wait. 6v ≡ -1 (mod z) and 6(1+6v) ≡ 6-36 = -30 (mod z). Not zero unless z | 30.
    -- Actually: from z | 6*(1+6v) and gcd(z,6)=1: z | 1+6v. And from z | 6v+1 (same): trivial.
    -- So far: z | 1+6v. NOW what?
    -- From u*z + v*x^3 = 1 and x^3 = z*c-6: u*z + v*(z*c-6) = 1. z*(u+vc) = 1+6v.
    -- SAME situation as before: z | 1+6v trivially because z*(u+vc) = 1+6v.
    -- Everything is circular!
    sorry
  sorry
