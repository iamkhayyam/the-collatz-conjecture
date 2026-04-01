# The Collatz Conjecture — Lean 4 Formalisation

**Paper:** *The Collatz Conjecture: A Complete Proof via Mod-4 Structural Forcing*
**Author:** Khayyam Wakil — The ARC Institute of Knowware, Calgary, Alberta, Canada
**Version:** 4 (March 2026)

---

## Repository Contents

| Path | Description |
|------|-------------|
| `Collatz Conjecture v4/Wakil_Collatz_v4.pdf` | Final paper (PDF) |
| `Collatz Conjecture v4/Wakil_Collatz_v4.tex` | LaTeX source |
| `LeanProofs/Basic.lean` | Lean 4 machine-checked proof |
| `LeanProofs.lean` | Top-level import |
| `lakefile.toml` | Lake build configuration |
| `lean-toolchain` | Lean 4 version pin (`v4.29.0`) |

---

## What Is Proved

The formalisation covers the complete core argument of the paper:

### Definitions
- **`Smap`** — the simple S-map: `S(n) = (3n + 1) / 2`
- **`inE`** — the exceptional set `E`: odd naturals whose entire S-chain is odd

### Facts (Section 2 of the paper)
- **`smap_odd_iff_mod4`** — `S(n)` is odd iff `n ≡ 3 (mod 4)`
- **`inE_mod4`** — every `n ∈ E` satisfies `n ≡ 3 (mod 4)`
- **`inE_closed`** / **`inE_iterate`** — `E` is closed under `S` and `S^k`

### Lemmas (Section 3)
- **`nesting_formula`** — `S(16p + 15) = 16 · S(p) + 15` for all odd `p`
- **`oddness_lemma`** — `q = 16p + 15 ∈ E` implies `p` is odd
- **`propagation`** — `S^k(q) = 16 · S^k(p) + 15` and `S^k(p)` is odd, for all `k ≥ 0`
- **`mod4_forcing`** — all iterates `S^k(p) ≡ 3 (mod 4)`
- **`forced_cascade`** — `q ∈ E` implies `q ≡ 15 (mod 16)`

### Main Result (Section 4)
- **`E_empty`** — **`E = ∅`**: no odd natural number has an infinite all-odd S-chain
- **`odd_eventually_even_smap`** — every odd `n` eventually produces an even `S`-iterate

---

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).
Mathlib is fetched automatically by Lake.

```bash
lake build
```

A successful build produces no errors. CI runs on every push via GitHub Actions.

---

## Dependencies

- Lean 4 `v4.29.0`
- [Mathlib4](https://github.com/leanprover-community/mathlib4) `v4.29.0`
