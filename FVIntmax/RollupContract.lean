import FVIntmax.Block

namespace Intmax

section RollupContract

/--
2.4

- Scontract := 𝔹*
-/
abbrev RollupState (K₁ K₂ V : Type) [OfNat V 0] [LE V] (C Sigma : Type) :=
  List (Block K₁ K₂ C Sigma V)

namespace RollupState

/--
2.4

- When the rollup contract is deployed to the blockchain, it is initialized with
  the state () consisting of the empty list.
-/
def initial (K₁ K₂ V : Type) [OfNat V 0] [LE V] (C Sigma : Type) : RollupState K₁ K₂ V C Sigma := []

end RollupState

/-
2.5
-/
section Depositing

/--
TODO(REVIEW): Does the order in which these get into the state matter? I'm choosing to prepend
              here because it's the more natural operation on `List` with better reduction behaviour.
              It's not a big deal tho, we can do `s ++ [Block.deposit addr value]` and then shuffle.
-/
def deposit {K₁ K₂ C Sigma V : Type} [OfNat V 0] [LE V]
            (addr : K₂) (value : {x : V // 0 ≤ x}) (s : RollupState K₁ K₂ V C Sigma) : RollupState K₁ K₂ V C Sigma :=
  Block.deposit addr value :: s

end Depositing


end RollupContract

end Intmax
