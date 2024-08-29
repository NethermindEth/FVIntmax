import FVIntmax.Block

namespace IntMax

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

end RollupContract
