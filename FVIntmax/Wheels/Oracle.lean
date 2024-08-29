import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finmap

namespace IntMax

/-
_Random oracle_ is an idealised model that associates a new unique value with every input it has not yet encountered.
In case the input was seen before, the previously assigned value is returned instead.
-/

section RandomOracle

/--
Random oracle state.
-/
structure RandomOracle (α : Type) (ω : Type) [Fintype ω] where
  m                 : Finmap (λ _ : α ↦ ω)

  /-
  NB several ways to skin this cat come to mind
  - #0 [ ] we could keep this as a `Finset` and then check if `availableCodomain = ∅` and
           noncomputably extract an element one by one from this set
  - #1 [x] we could use choice initially to construct a `List` from the codomain's underlying `Finset`
           initially and then forget about choice until the end of time
  - #2 [ ] can we cheat and do a direct `Fin ω` for the codomain? I have no idea, but would
           be the simplest model I think - use `Fin`'s linear order and keep a 'max' that has so far been allocated.
           Every new output then increments the max by one and returns it from the codomain.
           Does this break anything in a world with a global assumption that this cannot be inverted or reasoned about
           in any way, shape, or form?
           TODO(REVIEW): Can we do this or is this a very stupid question to ask :grin:?
           Note that there's a noncomputable bijection from `Fin` to any other `Finite` or `Fintype`
  -/
  availableCodomain : List ω

variable {α : Type} 
         {ω : Type} [Fintype ω] -- Fintype needed for `RandomOracle.initial` henceforth.

/--
NB using `#1`, so we magically (using `choice`) obtain a `List` of all the elements from the codomain.
This is convenient to simplify `hash`, hence this is chosen over `#0`.
-/
noncomputable def RandomOracle.initial : RandomOracle α ω :=
  {
    m                 := ∅
    availableCodomain := Finset.toList (Fintype.elems (α := ω))
  }

variable [DecidableEq α] -- Needed to distinguish seen and unseen keys.

/--
Random oracle function.

NB this is only computable because the process of creating the initial oracle state is not.
We are using `#1`.
-/
def hash (st : RandomOracle α ω) (x : α) : Option (ω × RandomOracle α ω) :=
  match st.m.lookup x with
  | .some val => .some (val, st)
  | .none     => match st.availableCodomain with
                 | [] => .none
                 | hd :: tl => .some (hd, { m := st.m.insert x hd, availableCodomain := tl })

end RandomOracle

end IntMax
