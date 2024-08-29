import Mathlib.Data.Finmap

/-
TODO(REVIEW): Not sure what > Task 2.1. Accounts entails for the time being :grin:.
              I have given it an honest go for now.
-/
namespace Intmax

/--
NB we do not need _yet_ that `V` is a lattice ordered abelian group.
What we _do_ need is some notion of what it means to be non-negative.
-/
structure Account (V : Type) [OfNat V 0] [LE V] :=
  balance : { v : V // 0 ≤ v }

def Accounts (K V : Type) [OfNat V 0] [LE V] :=
  Finmap (λ _ : K ↦ Account V)

end Intmax
