import Mathlib.Data.Nat.Defs
import Mathlib.Control.Random
import FVIntmax.Wheels.Wheels

namespace Intmax

/-
A - A.3  

NB `Σ` has a known meaning in Lean, so we diverge a little:
- `Σ = Sigma`
-/
section SignatureAggregation

open scoped SimpleRandom

set_option linter.unusedVariables false in
/--
TODO(REVIEW):
- As with `AuthenticatedDictionary`, the same `Λ` question; please cf. Definition 3 TODO(REVIEW)
  in https://github.com/NethermindEth/FVIntmax/pull/2.
- The 'randomness' is currently modelled trivially (cf. `Wheels/Wheels.lean`).
  Does it seem sensible? Do we need anything better than that? Actually, we could probably
  even get away with less?
-/
structure SignatureAggregation (M Kₚ Kₛ Sigma : Type) where
  Λ         : ℕ

  KeyGen    : ℕ → SimpleRandom.Seed → Kₚ × Kₛ
  Sign      : ℕ → Kₛ → M → Sigma
  Aggregate : ℕ → List (Kₚ × Sigma) → Sigma
  Verify    : ℕ → List Kₚ → M → Sigma → Bool

  /--
  Definition 6

  TODO(WARN): This definition is subject to change specifically to replace `List.unzip/unzip` with
              `List.map Prod.fst/snd`, we will see what lemmas there are in mathlib, but the idea
              for the time being is that the relationship between `kₚ` and `kₛ` is more explicit
              if `unzip` and `zip` are used.
  -/
  Correctness : ∀ (l : List (Kₚ × Kₛ)) (h : ∀ pair ∈ l, pair ←ᵣ KeyGen Λ) (m : M), 
                  let (kₚs, kₛs) := l.unzip
                  Verify Λ kₚs m (Aggregate Λ (kₚs.zip (kₛs.map (Sign Λ · m)))) = true

  /--
  Definition 7

  TODO(REVIEW): It is unclear to me from the definition as to where the secret key should come from
                for the: > 'belongs to an honest user who didn’t sign the message m with their secret key',
                but here I am assuming that every `Kₚ` has an associated `Kₛ` and I consider this pair
                to be 'a user'.
  -/
  Unforgeability :
    ComputationallyInfeasible <|
      ∃ (k : List (Kₚ × Kₛ)) (m : M) (σ : Sigma),
        let kₚs := k.map Prod.fst
        Verify Λ kₚs m σ = true ∧
        -- PAPER: and where one of the public keys (pki)i∈[n] belongs to an honest user who didn’t
        -- sign the message m with their secret key.
        ∃ userIdx : Fin k.length,
          let (honestₚ, honestₛ) := k[userIdx]
          honestₚ ∈ kₚs ∧ ∃ key : Kₛ, key ≠ honestₛ ∧ Sign Λ key m = σ 
     
end SignatureAggregation

end Intmax
