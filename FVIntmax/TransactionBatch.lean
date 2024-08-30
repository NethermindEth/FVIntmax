import Mathlib.Data.Finmap

namespace Intmax

/-
2.6 - Transaction batch
-/
section TransactionBatch

/--
PAPER: K := K1 ⨿ K2

TODO(REVIEW): Can we assume that `addr₁ : K₁` and `addr₂ : K₂` are incomparable?
              This is currently based on this assumption, as we have automatically
              `[DecidableEq (K₁ ⊕ K₂)]` given `[DecidableEq K₁]` and `[DecidableEq K₂`],
              but the instance compares e.g. `.inl 42 : Key Nat Nat`
              and `.inr 42 : Key Nat Nat` _UNEQUAL_.

              Of course this is fixable, essentially I'm just wondering if L₁ addresses can coincide with L₂ addresses. 
-/
abbrev Key (K₁ K₂ : Type) := K₁ ⊕ K₂

/--
PAPER: a transaction batch is an element of Vᵏ₊
NB as per usual, V does not need to be a latticed-ordered abelian group just yet.
-/
abbrev TransactionBatch (K₁ K₂ V : Type) [OfNat V 0] [LE V] := Finmap (λ _ : Key K₁ K₂ ↦ {v : V // 0 ≤ v})

end TransactionBatch

end Intmax
