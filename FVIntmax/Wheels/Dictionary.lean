import Mathlib.Data.Finmap

import FVIntmax.Wheels.Wheels

namespace Intmax

/-
A - A.1
-/
section Dictionaries

variable {K V : Type}

/--
Definition 1

TODO(REVIEW): I _think_ the `m` is to be understood as total with respect to `keys`.
              As such, `total` established `k ∈ m`, which then gives `m.lookup k = some _`.

Feel free to ignore this bit:
              This lets us remove all the `Option`s without artifically returning a default element for keys not in the map.
              Of course, the price is the proof obligation for `h : k ∈ m` at the point of lookup, which cannot be avoided anyway,
              merely postponed in case we wanted to be in `Option` and prove under the assumption `Option.isSome`,
              or alternatively, not be in `Option` and prove under the assumption `m.lookup k ≠ default`(-ish).
              NB. there are some functions in `section Lookup` marked `@[deprecated]` that implement all of the options.
              
              While it is normally a _good_ idea to postpone these obligations (shoo dependent types),
              there are two key considerations for which I opted for this:
                - #0: It makes the subsequent definitions correlate more closely with the way they are written in the paper.
                - #1: I hope the `k ∈ m` relationship is in many cases provable automatically with a bit of Lean magic.
                      If this turns out not to be the case, I'll refactor the solution to save a bit of time in the future.
-/
structure Dict (K V : Type) : Type :=
  keys  : Set K
  -- `Vᵏ`
  m     : Finmap (λ _ : K ↦ V)
  -- I hope the ethos here is that `Vᵏ` is total over the set of `keys`.
  total : ∀ {k : K}, k ∈ keys ↔ k ∈ m

section Dict

variable {dict : Dict K V} {k : K} [DecidableEq K]

def Dict.contains (k : K) (dict : Dict K V) : Prop := k ∈ dict.m

/--
Enables the notation:
- `key ∈ dict`

NB - Considering `k ∈ keys ↔ k ∈ m`, we choose `k ∈ m` arbitrarily and always get the other one for free.

- `k ∈ dict = dict.contains k`
-/
instance : Membership K (Dict K V) := ⟨Dict.contains⟩

/--
`k ∈ dict` is decidable. Useful for development.
-/
instance : Decidable (k ∈ dict) := inferInstanceAs (Decidable (k ∈ dict.m))

namespace Dict

section Mem

/-
Henceforth, we will give preference to statements using `x ∈ dict` rather than `x ∈ dict.m` or
`x ∈ dict.keys`, even though these notions are all equal by virtue of `Dict.total` and `Dict.contains`,
as witnessed by the lemmas in this section.
This is because I would prefer to formulate all subsequent lemmas using a single notion, rather than
awkwardly shuffle. The choice is made almost arbitrarily but this is technically 'the most abstract'.

That said, I think it wise to keep statements that come directly from the paper as close to how they are
in the paper. As such, when it says that 'some k is in the set of keys of the dictionary', the Lean statement
will say `k ∈ dict.keys`. 

Slightly counter-intuitively, I will teach `aesop` (one way of doing automation in Lean)
to normalise to `k ∈ dict.keys` - the normalisation is useful so that the automation sees all relevant
lemmas and this specific form seems like the simplest to reason about; this is subject to change
if I find the other way more convenient in subsequent proofs. As such, `aesop` sees
`dict.keys > dict.m > dict` as expressed by the `aesop` tag on the lemmas below that gives
preference to the natural way of rewriting (i.e. replace lhs with rhs).
-/
@[aesop norm (rule_sets := [Intmax.aesop_dict])]
lemma mem_dict_iff_mem_map : k ∈ dict ↔ k ∈ dict.m := by rfl

@[aesop norm (rule_sets := [Intmax.aesop_dict])]
lemma mem_map_iff_mem_keys : k ∈ dict.m ↔ k ∈ dict.keys := dict.total.symm

/-
Just ignore this section.
-/
section AutomateMembership

open Lean.Elab.Tactic in
/--
`dict` tries to automatically resolve membership in dictionaries.
- uses the `Intmax.aesop_dict` set
-/
elab "dict" : tactic => do
  evalTactic <| ← `(tactic| (aesop (rule_sets := [Intmax.aesop_dict]); done))

/--
Resolve membership proof obligation by the custom `dict` tactic.
Thus, `dict[k]` will conceptually do `dict[k]'(by dict)`.
Cf. `Definition 1`, discussion `#1`.
-/
macro_rules | `(tactic| get_elem_tactic_trivial) =>
              `(tactic| first | trivial | simp (config := { arith := true }); done | omega | dict)

end AutomateMembership

end Mem

section Lookup

/--
NB As mentioned, I am hoping automation makes most of the membership yoga transparent.
It is reasonably simple to switch to a different option as per discussion in `Definition 1`.
Subject to change therefore.

Total by construction. Needs `h : k ∈ dict` but we sprinkle Lean dust and hope this is transparent most of the times.
-/
def lookup {k : K} (dict : Dict K V) : k ∈ dict → V := dict.m.lookup_h

/--
Partial. In `Option`. Needs `h : (dict.lookup k).isSome`.
-/
@[deprecated]
def lookup? (k : K) (dict : Dict K V) : Option V := dict.m.lookup k

/--
Total. Needs `h : (dict.lookup k).isSome`.
-/
@[deprecated]
def lookupD (k : K) (d : V) (dict : Dict K V) : V := dict.m.lookup k |>.getD d

end Lookup

end Dict

/--
Enables the notation:
- `dict[k]'h`
-/
instance : GetElem (Dict K V) K V (λ dict k ↦ k ∈ dict) := ⟨λ dict _ h ↦ dict.lookup h⟩

namespace Dict

section Merge

/-
Equip `K` with lawful equality. This is necessary for `Dict.Merge`.
-/
variable [DecidableEq K]

/--
Definition 2

NB - From the paper, we have `D₁(k), if k ∈ K₁`, i.e. the merge is _left biased_.
     This just happens to be the case `Finmap.union`, see the sanity-check `example` below.
-/
def Merge (dict₁ dict₂ : Dict K V) : Dict K V :=
  {
    keys  := dict₁.keys ∪ dict₂.keys
    m     := dict₁.m ∪ dict₂.m
    total := by cases dict₁; cases dict₂; aesop
  }
  
end Merge

end Dict

/--
Enables the notation:
- `dict₁ ∪ dict₂`
-/
instance : Union (Dict K V) := ⟨Dict.Merge⟩ 

-- NB (d₁ ∪ d₂)[2] works without an explicit proof that `2 ∈ (d₁ ∪ d₂)` and yet is in `Nat`, not in `Option Nat`.
-- example : let d₁ : Dict ℕ ℕ := ⟨{1, 2}, ⟨Multiset.ofList [⟨1, 42⟩, ⟨2, 1337⟩], sorry⟩, sorry⟩
--           let d₂ : Dict ℕ ℕ := ⟨{2, 3}, ⟨Multiset.ofList [⟨2, 24601⟩, ⟨2, 0xdeadbeef⟩], sorry⟩, sorry⟩
--           (d₁ ∪ d₂)[2] = 1337 := rfl

namespace Merge

section Merge

variable {dict₁ dict₂ : Dict K V}

section Projections

@[simp]
lemma m_union_eq : (dict₁ ∪ dict₂).m = dict₁.m ∪ dict₂.m := rfl

@[simp]
lemma keys_union_eq : (dict₁ ∪ dict₂).keys = dict₁.keys ∪ dict₂.keys := rfl

end Projections

section Mem

@[simp]
lemma mem_union : k ∈ dict₁ ∪ dict₂ ↔ k ∈ dict₁ ∨ k ∈ dict₂ := by
  simp [Dict.mem_dict_iff_mem_map]

end Mem

end Merge

end Merge

end Dict

end Dictionaries

end Intmax
