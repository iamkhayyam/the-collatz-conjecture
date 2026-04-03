/-
  LeanProofs/Basic.lean
  Lean 4 formalisation of:
    "The Collatz Conjecture: A Complete Proof via Mod-4 Structural Forcing"
    by Khayyam Wakil, Version 4 — March 2026

  We formalise the core S-map theory (Sections 2–4 of the paper):
    • Definition of S and the exceptional set E
    • Facts 2.1–2.3 (parity, E ⊆ 3 mod 4, closure)
    • Lemma 3.1 (Forced Cascade: E ⊆ 15 mod 16)
    • Lemma 3.2 (Nesting Formula)
    • Lemma 3.3 (Oddness Lemma)
    • Lemma 3.4 (Inductive Propagation)
    • Lemma 3.5 (Mod-4 Forcing)
    • Theorem 4.1 (E = ∅)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

open Nat

-- ============================================================
--  Section 2: Definitions and elementary facts
-- ============================================================

/-- The simple S-map: S(n) = (3n + 1) / 2, defined on all natural numbers.
    For odd n, this equals (3n+1)/2 exactly. -/
def Smap (n : ℕ) : ℕ := (3 * n + 1) / 2

/-- The exceptional set E: odd naturals whose S-chain is always odd.
    We say n ∈ E iff n is odd and S^k(n) is odd for all k ≥ 0. -/
def inE (n : ℕ) : Prop :=
  Odd n ∧ ∀ k : ℕ, Odd (Smap^[k] n)

/-- Fact 2.1: For odd n, S(n) is odd iff n ≡ 3 (mod 4). -/
theorem smap_odd_iff_mod4 (n : ℕ) (hn : Odd n) :
    Odd (Smap n) ↔ n % 4 = 3 := by
  rw [Nat.odd_iff] at hn ⊢
  simp only [Smap]
  omega

/-- Fact 2.2: Every n ∈ E satisfies n ≡ 3 (mod 4). -/
theorem inE_mod4 (n : ℕ) (hE : inE n) : n % 4 = 3 := by
  have h1 := hE.2 1
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at h1
  exact (smap_odd_iff_mod4 n hE.1).mp h1

/-- Fact 2.3: E is closed under S. If n ∈ E then S(n) ∈ E. -/
theorem inE_closed (n : ℕ) (hE : inE n) : inE (Smap n) := by
  refine ⟨?_, fun k => ?_⟩
  · have := hE.2 1
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at this
    exact this
  · have := hE.2 (k + 1)
    simp only [Function.iterate_succ, Function.comp] at this ⊢
    exact this

/-- Closure under S extended to k-fold iterates. -/
theorem inE_iterate (n : ℕ) (hE : inE n) (k : ℕ) : inE (Smap^[k] n) := by
  induction k with
  | zero => simpa
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp]
    exact inE_closed _ ih

-- ============================================================
--  Section 3: The Lemmas
-- ============================================================

/-- Lemma 3.2 (Nesting Formula): For every odd p, S(16p + 15) = 16 · S(p) + 15. -/
theorem nesting_formula (p : ℕ) (hp : Odd p) :
    Smap (16 * p + 15) = 16 * Smap p + 15 := by
  rw [Nat.odd_iff] at hp
  simp only [Smap]
  omega

/-- Lemma 3.3 (Oddness Lemma): If q ∈ E and q = 16p + 15, then p is odd.

    Proof: If p is even, then q = 32s + 15 for some s.
    Direct computation shows S⁴(q) is even, contradicting q ∈ E. -/
theorem oddness_lemma (p q : ℕ) (hq : q = 16 * p + 15) (hE : inE q) :
    Odd p := by
  rw [Nat.odd_iff]
  by_contra heven
  push Not at heven
  have hp_even : p % 2 = 0 := by omega
  -- S⁴(q) must be odd (from hE), but we show it's even
  have h4 := hE.2 4
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at h4
  rw [hq] at h4
  simp only [Smap] at h4
  rw [Nat.odd_iff] at h4
  omega

/-- Lemma 3.4 (Inductive Propagation):
    If q = 16p + 15 ∈ E with p odd, then for all k:
    (a) S^k(q) = 16 · S^k(p) + 15
    (b) S^k(p) is odd -/
theorem propagation (p q : ℕ) (hq : q = 16 * p + 15) (hE : inE q) (hp : Odd p) :
    ∀ k : ℕ, Smap^[k] q = 16 * Smap^[k] p + 15 ∧ Odd (Smap^[k] p) := by
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id]
    exact ⟨by omega, hp⟩
  | succ k ih =>
    obtain ⟨ih_eq, ih_odd⟩ := ih
    constructor
    · simp only [Function.iterate_succ', Function.comp]
      rw [ih_eq]
      exact nesting_formula (Smap^[k] p) ih_odd
    · simp only [Function.iterate_succ', Function.comp]
      have h_eq : Smap (Smap^[k] q) = 16 * Smap (Smap^[k] p) + 15 := by
        rw [ih_eq]
        exact nesting_formula (Smap^[k] p) ih_odd
      have h_inE := inE_iterate q hE (k + 1)
      rw [Function.iterate_succ', Function.comp] at h_inE
      exact oddness_lemma (Smap (Smap^[k] p)) (Smap (Smap^[k] q)) h_eq h_inE

/-- Lemma 3.5 (Mod-4 Forcing): Under propagation hypotheses,
    every S^k(p) ≡ 3 (mod 4). -/
theorem mod4_forcing (p q : ℕ) (hq : q = 16 * p + 15) (hE : inE q) (hp : Odd p) :
    ∀ k : ℕ, Smap^[k] p % 4 = 3 := by
  intro k
  have ⟨_, hk_odd⟩ := propagation p q hq hE hp k
  have ⟨_, hk1_odd⟩ := propagation p q hq hE hp (k + 1)
  simp only [Function.iterate_succ', Function.comp] at hk1_odd
  exact (smap_odd_iff_mod4 (Smap^[k] p) hk_odd).mp hk1_odd

/-- Helper: if n is odd and S(n) is odd, then n % 4 = 3. -/
theorem odd_smap_odd_mod4 (n : ℕ) (hn : n % 2 = 1) (hs : Smap n % 2 = 1) :
    n % 4 = 3 := by
  simp only [Smap] at hs
  omega

/-- Helper: if n % 4 = 3 and S(n) is odd and S²(n) is odd, then n % 16 ∈ {7, 15}. -/
theorem smap_mod16_step2 (n : ℕ) (hn4 : n % 4 = 3)
    (h1 : Smap n % 2 = 1) (h2 : Smap (Smap n) % 2 = 1) :
    n % 16 = 7 ∨ n % 16 = 15 := by
  simp only [Smap] at h1 h2
  omega

/-- Helper: if n % 16 = 7 and S(n), S²(n), S³(n) all odd, contradiction. -/
theorem no_mod16_eq_7 (n : ℕ) (hmod : n % 16 = 7)
    (h1 : Smap n % 2 = 1) (h2 : Smap (Smap n) % 2 = 1)
    (h3 : Smap (Smap (Smap n)) % 2 = 1) : False := by
  simp only [Smap] at h1 h2 h3
  omega

/-- Lemma 3.1 (Forced Cascade): If q ∈ E, then q ≡ 15 (mod 16).

    All odd residues mod 16 except 15 produce an even S-iterate within 4 steps.
    We break this into helper lemmas to avoid omega timeouts. -/
theorem forced_cascade (q : ℕ) (hE : inE q) : q % 16 = 15 := by
  have hmod4 := inE_mod4 q hE
  -- Extract oddness of first few iterates
  have hodd := hE.1
  rw [Nat.odd_iff] at hodd
  have h1 := hE.2 1
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at h1
  rw [Nat.odd_iff] at h1
  have h2 := hE.2 2
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at h2
  rw [Nat.odd_iff] at h2
  have h3 := hE.2 3
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id] at h3
  rw [Nat.odd_iff] at h3
  -- q % 4 = 3 means q % 16 ∈ {3, 7, 11, 15}
  -- Step 1: eliminate 3 and 11 (they produce even S(q) or S²(q))
  have h_not_3_11 : q % 16 = 7 ∨ q % 16 = 15 := smap_mod16_step2 q hmod4 h1 h2
  -- Step 2: eliminate 7 (produces even value within 3 steps)
  rcases h_not_3_11 with h7 | h15
  · exact (no_mod16_eq_7 q h7 h1 h2 h3).elim
  · exact h15

-- ============================================================
--  Section 4: Main Result
-- ============================================================

/-- Theorem 4.1: E = ∅. The exceptional set is empty.

    Proof by strong induction (well-ordering).
    Any q ∈ E has q ≡ 15 (mod 16), so p := (q-15)/16 < q.
    By oddness lemma p is odd, by propagation p ∈ E.
    This contradicts minimality. -/
theorem E_empty : ∀ n : ℕ, ¬ inE n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hE
    have hmod := forced_cascade n hE
    set p := n / 16 with hp_def
    have hn : n = 16 * p + 15 := by omega
    have hp_odd := oddness_lemma p n hn hE
    have hp_lt : p < n := by omega
    have hp_inE : inE p := by
      refine ⟨hp_odd, fun k => ?_⟩
      exact (propagation p n hn hE hp_odd k).2
    exact ih p hp_lt hp_inE

-- ============================================================
--  Corollary: Consequences
-- ============================================================

/-- The Collatz map T. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Every odd positive integer eventually produces an even S-iterate.
    Direct consequence of E = ∅. -/
theorem odd_eventually_even_smap (n : ℕ) (hn : Odd n) :
    ∃ k : ℕ, ¬ Odd (Smap^[k] n) := by
  by_contra h
  push Not at h
  exact E_empty n ⟨hn, h⟩

-- ============================================================
--  Bridge Lemmas (Sections 4.2–4.4 of the paper)
-- ============================================================

/-- Parity obstruction: 3^a ≠ 2^b for a, b ≥ 1.
    3^a is always odd; 2^b is always even. These are disjoint. -/
theorem three_pow_ne_two_pow (a b : ℕ) (_ha : a ≥ 1) (hb : b ≥ 1) :
    3 ^ a ≠ 2 ^ b := by
  have h_odd : Odd (3 ^ a) := by apply Odd.pow; decide
  have h_even : Even (2 ^ b) := by
    apply Even.pow_of_ne_zero (⟨1, by ring⟩)
    omega
  intro heq
  rw [heq] at h_odd
  rw [Nat.odd_iff] at h_odd
  rw [Nat.even_iff] at h_even
  omega

/-- Lemma 4.2 (Paper): No non-trivial T-cycles exist.
    The only cycle of the Collatz map T on ℕ is {1, 2}.

    STATUS: The key step is sorried — see note below.

    The paper's proof (lines 472–484) argues: any odd element n₀ of a T-cycle
    has S^k(n₀) all odd (since they stay in the finite cycle), so n₀ ∈ E = ∅.

    GAP: This argument implicitly uses the *compressed* S-map Sᶜ (which always
    outputs odd values by construction). But `inE` here uses the *simple* S-map
    Smap, which can output even values when n ≡ 1 (mod 4). An element in a
    T-cycle can have Smap(n) even without contradiction — it would simply not
    be in E. So the paper's route does not directly apply to `inE`.

    CORRECT APPROACH (not yet formalised): The orbit equation for a T-cycle
    with a odd steps and b even steps is 3^a · n₀ + c = 2^b · n₀ (c > 0).
    `three_pow_ne_two_pow` handles the a = b sub-case. The full derivation
    that no n₀ > 2 satisfies the orbit equation requires additional arithmetic
    machinery. -/
theorem no_nontrivial_cycles (n : ℕ) (hn : n > 2) (K : ℕ) (hK : K > 0) :
    collatz^[K] n ≠ n := by
  sorry

/-- Lemma 4.3 (Paper): No T-orbit is unbounded.

    STATUS: Sorried — see note below.

    The paper's proof has two sub-cases:
    • ℓ = 1: n' = (3n*+1)/2^j with j ≥ 2, giving n' ≤ (3n*+1)/4 < n*. Clean.
    • ℓ ≥ 2: the paper falls back on "n* sufficiently large" or the
      computational bound n < 2^68, neither of which closes in Lean.

    The ℓ ≥ 2 sub-case is the remaining gap for this lemma. -/
theorem no_divergent_orbits (n : ℕ) :
    ∃ M : ℕ, ∀ k : ℕ, collatz^[k] n ≤ M := by
  sorry

/-- Corollary 4.4 (Paper): Every positive integer's Collatz orbit reaches 1.

    STATUS: Sorried pending `no_nontrivial_cycles` and `no_divergent_orbits`.

    Once both bridge lemmas are proved, this follows by:
    (1) the orbit is bounded (no_divergent_orbits),
    (2) the only cycle is {1,2} (no_nontrivial_cycles),
    (3) a bounded orbit must eventually repeat, and the only repeat
        permitted is the {1,2} cycle, so 1 must be reached. -/
theorem collatz_convergence (n : ℕ) (hn : n ≥ 1) :
    ∃ k : ℕ, collatz^[k] n = 1 := by
  sorry
