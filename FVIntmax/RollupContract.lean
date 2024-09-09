import Mathlib.Data.Fintype.Basic

import FVIntmax.Wheels.Oracle
import FVIntmax.Wheels.Wheels

import FVIntmax.Block
import FVIntmax.TransactionBatch
import FVIntmax.Wheels

namespace Intmax

section RollupContract

/--
2.4

- Scontract := 𝔹*
-/
def RollupState (K₁ K₂ V : Type) [OfNat V 0] [LE V] (C Sigma : Type) :=
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
            (addr : K₂) (value : { x : V // 0 ≤ x }) (s : RollupState K₁ K₂ V C Sigma) : RollupState K₁ K₂ V C Sigma :=
  Block.deposit addr value :: s

end Depositing

/-
2.6
-/
section Transferring

variable {K₁ : Type} [DecidableEq K₁] [Finite K₁]
         {K₂ : Type} [Finite K₂]
         {sender sender' : K₂} {senders : List K₂}
         {V : Type} [DecidableEq V] [Finite V]

/-
Phase 1
-/

noncomputable def salt : UniquelyIndexed K₂ := default

/--
This is a corollary following from the way that `UniquelyIndexed` types are constructed.
-/
theorem salt_injective : Function.Injective (salt (K₂ := K₂)) := salt.injective

noncomputable def salts : List K₂ → List (UniqueTokenT K₂) := List.map salt

/--
The only relevant property of salts.
-/
theorem injective_salts : Function.Injective (salts (K₂ := K₂)) :=
  List.map_injective_iff.2 salt.injective

section Transaction

variable [DecidableEq K₂]

/--
PAPER:
- hₛ ← H(tₛ, saltₛ)
-/
noncomputable def H : UniquelyIndexed (TransactionBatch K₁ K₂ V × UniqueTokenT K₂) := default

theorem injective_H : Function.Injective (H (K₁ := K₁) (K₂ := K₂) (V := V)) := H.injective

/--
TODO(REVIEW) - Re. @Denisa wrt. one salt per one transaction;

I actually think this first step is correct irrespective of salting multiple transactions.
This is because this definition takes: `senders : List (K₂ × TransactionBatch K₁ K₂ V)`, IOW
it already only expresses the relationship of a single batch being sent by each user.

As such, if there is some other definition further down the line that expresses the notion of transactions
being sent over and over or whatever else, the first step will repeat and you get a new salt - note that in this model,
you can't actually prove that the new salt is distinct (or even the same, for that matter), and this to me seems
like actually a good thing.
-/
noncomputable def firstStep
  (senders : List (K₂ × TransactionBatch K₁ K₂ V)) : List (UniqueTokenT (TransactionBatch K₁ K₂ V × UniqueTokenT K₂)) :=
  let (users, batches) := senders.unzip
  let salts := salts users
  List.zipWith (Function.curry H) batches salts

theorem injective_firstStep : Function.Injective (firstStep (K₁ := K₁) (K₂ := K₂) (V := V)) := by
  unfold firstStep
  simp [salts]; simp [Function.Injective]

end Transaction

end Transferring

end RollupContract

end Intmax
