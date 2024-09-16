import Mathlib.Data.Finite.Basic
import Mathlib.Data.Finmap
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset

import FVIntmax.Key
import FVIntmax.Wheels.Wheels
import FVIntmax.Wheels

import Mathlib.Tactic

namespace Intmax

/-
2.6 - Transaction batch
-/
section TransactionBatch

/--
PAPER: a transaction batch is an element of V₊ᵏ
NB we do not impose `V₊`, here, but in `TransactionBatch.isValid` for convenience.
As such, we will prove properties for _valid transaction batches_ rather than for any batches.
NB as per usual, V does not need to be a latticed-ordered abelian group just yet.
-/
abbrev TransactionBatch (K₁ : Type) [Finite K₁] (K₂ : Type) [Finite K₂] (V : Type) :=
  { m : Finmap (λ _ : Key K₁ K₂ ↦ V) // ∀ k, k ∈ m }

/--
A _valid transaction batch_ only contains nonnegative values of `V`.
NB there is now a restriction on `V` such that the notion of nonnegative makes sense.
-/
abbrev TransactionBatch.isValid {K₁ : Type} [Finite K₁] [DecidableEq K₁]
                                {K₂ : Type} [Finite K₂] [DecidableEq K₂] [LE V] [OfNat V 0]
  (tb : TransactionBatch K₁ K₂ V) := isCodomainNonneg tb.1

section Finite

variable {K₁ : Type} [Finite K₁]
         {K₂ : Type} [Finite K₂]

set_option linter.unusedVariables false in
/--
We define an equivalence between maps `K → V` and finmaps that are defined for all keys.
This will be used to show that `TransactionBatch` is finite as long as the domain and codomain
is finite.
-/
noncomputable def univFinmap (K : Type) [Fintype K] [DecidableEq K]
                             (V : Type) [DecidableEq V] [Fintype V] :
  { m : Finmap (λ _ : K ↦ V) // ∀ k, k ∈ m } ≃ (K → V) :=
  {
    toFun := λ m k ↦ m.1.lookup_h (a := k) (m.2 k)
    invFun := λ f ↦
      let fvals := { Sigma.mk x (f x) | x : K }
      have : Fintype ↑fvals := by
        apply Fintype.subtype (s := { Sigma.mk x (f x) | x : K })
        aesop
      ⟨⟨
        Multiset.ofList fvals.toFinset.toList,
        by /-
             We start with no duplicates in the universal set for `K` and
             the production of pairs `(k : K × f k : V)` keeps them intact.
             As such, there are no duplicate keys in the final map.
           -/
           simp only [
             Finset.mem_univ, true_and, Set.toFinset_setOf, Finset.univ_filter_exists,
             Finset.coe_toList, Finset.image_val, fvals
           ]
           rw [←Multiset.nodup_keys]
           have : (Finset.univ.val (α := K)).Nodup := Finset.nodup _
           rwa [Multiset.keys_dedup_map_pres_univ this (by simp)]
           ⟩,
        by /-
             We start with the universal set for `K`, which is complete by definiton.
             Furthermore, we keep all `K`s and assign them values from the function's range.
             This construction obviously preserves all keys.
           -/
           simp only [
             Finset.mem_univ, true_and, Set.toFinset_setOf, Finset.univ_filter_exists,
             Finset.coe_toList, Finset.image_val, true_implies, fvals
           ]
           intros k
           rw [Finmap.mem_def]; dsimp
           rw [Multiset.keys_dedup_map_pres_univ (Finset.nodup _) (by simp)]
           simp only [Finset.mem_val, Finset.mem_univ]
           ⟩
    left_inv := by
      /-
        Two key observations:
        - `⟨k, v⟩ ∈ m` iff `m.lookup k = v`
        - in maps where all keys are present, the lookup on the universal set of all keys never fails
      -/
      simp [Function.LeftInverse]
      rintro ⟨m, hm⟩ h
      simp only [Finmap.lookup_h, Finmap.mk.injEq]
      rw [
        Multiset.dedup_eq_self.2 (Multiset.nodup_map_of_pres_keys_nodup (λ _ ↦ rfl) (Finset.nodup _)),
        Multiset.ext
      ]
      intros kv
      set m' := (Multiset.map (λ x ↦ _ : K → (_ : K) × V) _) with eqm'
      have nodupm' : m'.Nodup := Multiset.nodup_map_of_pres_keys_nodup (by simp) (Finset.nodup _)
      have nodupm : m.Nodup := by
        rwa [← Multiset.nodup_keys, Multiset.keys, Multiset.nodup_map_iff_of_inj_on] at hm
        rintro ⟨x₁, x₂⟩ hx ⟨y₁, y₂⟩ hy h'
        set map' : Finmap (λ _ : K ↦ V) := { entries := m, nodupKeys := _ }
        have eq₁ : ⟨x₁, x₂⟩ ∈ map'.entries := by aesop
        have eq₂ : ⟨x₁, y₂⟩ ∈ map'.entries := by aesop
        rw [←Finmap.lookup_eq_some_iff] at eq₁ eq₂
        aesop -- cc is too slow here but it works...
      rw [Multiset.count_eq_of_nodup nodupm', Multiset.count_eq_of_nodup nodupm]
      set map' : Finmap (λ _ : K ↦ V) := { entries := m, nodupKeys := hm } with eqm
      by_cases eq : kv ∈ m <;> (rcases kv with ⟨k, v⟩; simp [eq])
      · by_contra contra
        simp [eqm'] at contra
        have : ⟨k, v⟩ ∈ map'.entries := by aesop
        rw [←Finmap.lookup_eq_some_iff] at this
        simp [Option.get] at contra; split at contra; cc
      · simp [m']
        intros contra
        simp [Option.get] at contra; split at contra
        next _ _ _ _ eq₃ _ =>
          rw [Finmap.lookup_eq_some_iff] at eq₃; simp at eq₃
          aesop -- cc is too slow here but it works...
    right_inv := by
      /-
        Triviall follows from `⟨k, v⟩ ∈ m` iff `m.lookup k = v`.
        The left inverse is more involved because we need do not get the functional property of
        `f : K → V` for free and we have to recover it.
      -/
      simp [Function.RightInverse, Function.LeftInverse]
      intros f; ext
      simp [Finmap.lookup_h, Option.get]
      split
      next _ _ _ _ e _ => 
        simp [Finmap.lookup_eq_some_iff] at e
        exact e.symm
  }

/--
For a finite K₁, K₂ and V, we can establish that a `TransactionBatch K₁ K₂ V` is finite.
-/
instance [Finite V] [DecidableEq K₁] [DecidableEq K₂] [DecidableEq V] :
  Finite (TransactionBatch K₁ K₂ V) := by
  /-
    Follows trivially from the definition of `univFinmap`, for if we know that `(Key K₁ K₂ → V)`
    is finite and we have a `... ≃ TransactionBatch K₁ K₂ V`, then the rhs is finite as well.
  -/
  have : Fintype K₁ := Fintype.ofFinite _
  have : Fintype K₂ := Fintype.ofFinite _
  have : Fintype V := Fintype.ofFinite _
  exact @Finite.of_equiv _ _ _ (univFinmap (K := Key K₁ K₂) (V := V)).symm

/-
TODO(REVIEW):
  Suppose we have the same theorem:
  instance {K₁ : Type} [Finite K₁] [DecidableEq K₁]
           {K₂ : Type} [Finite K₂] [DecidableEq K₂]
           {V  : Type} [Finite V] [DecidableEq V] : Finite (TransactionBatch K₁ K₂ V)  

  But instead we define `TransactionBatch K₁ K₂ V` to be a `Finmap ((_ : Key K₁ K₂) ↦ V)`.
  Can we easily show that this is finite too? I think this would be more convenient,
  but I couldn't easily prove this so I chose a slightly different approach.

  Does the `univFinmap` maybe help?
-/

end Finite

end TransactionBatch

end Intmax
