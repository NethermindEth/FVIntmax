import Mathlib
import Mathlib.Algebra.Group.Int

import FVIntmax.BalanceProof
import FVIntmax.Block
import FVIntmax.Key
import FVIntmax.RollupContract
import FVIntmax.Wheels

import FVIntmax.Wheels.Dictionary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Intmax

open Classical -- Don't care :).

/-
Appendix B - Computing balances
-/
section Balance

variable {Pi : Type}
         {K₁ : Type} [Finite K₁]
         {K₂ : Type} [Finite K₂]
         {V : Type} [Finite V]
         {C Sigma : Type}

/--
PAPER: Formally, let K := K1 ⨿ K2 ⨿ {Source}
-/
inductive Kbar (K₁ K₂ : Type) where
  | key (k : Key K₁ K₂)
  | Source
deriving DecidableEq

instance : Coe (Key K₁ K₂) (Kbar K₁ K₂) := ⟨.key⟩

/--
NB not important. There's an obvious equivalence between the inductive `Kbar` and the
`Key K₁ K₂ ⊕ Unit` sum, which we can infer is finite given the `Key` is finite.
I prefer the wrapped inductive.
-/
def univKbar : Kbar K₁ K₂ ≃ Key K₁ K₂ ⊕ Unit :=
  {
    toFun := λ kbar ↦ match kbar with | .key k => k | .Source => ()
    invFun := λ sum ↦ match sum with | .inl k => .key k | .inr _ => .Source
    left_inv := by simp [Function.LeftInverse]; aesop
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  }

instance : Finite (Kbar K₁ K₂ : Type) :=
  Finite.of_equiv _ univKbar.symm
  
/--
NB we use Lean's natural associativity for products to get some freebies.
As such, our tuples are technically `(a, (b, c))` here. Obviously, this is associative
so not much changes.

NB further, we postpone nonnegativity of V into `Τ.isValid`.
-/
abbrev Τ (K₁ K₂ V : Type) := Kbar K₁ K₂ × Kbar K₁ K₂ × Option V

noncomputable instance : Fintype V := Fintype.ofFinite _

def Τ.isValid (τ : Τ K₁ K₂ V) [LE V] [OfNat V 0] :=
  match τ with
  | (s, r, v) => s ≠ r ∧ v.elim True (0 ≤ ·) ∧ s matches .Source → v.isSome 

/--
PAPER: complete transactions, consisting of the transactions
((s, r), v) ∈ T where v ̸= ⊥
-/
def Τ.isComplete [LE V] [OfNat V 0] (τ : Τ K₁ K₂ V) :=
  τ.isValid ∧ match τ with | (_, _, v) => v.isSome

/-
B.1 Step 1: Extracting a list of partial transaction
-/
section Extraction

section Deposit

def TransactionsInBlock_deposit (b : { b : Block K₁ K₂ C Sigma V // b.isDepositBlock }) : List (Τ K₁ K₂ V) :=
  match h : b.1 with
  | .deposit r v => [(.Source, r, v)]
  | .withdrawal .. | .transfer .. => by aesop

end Deposit

section Order

variable [LinearOrder K₁] [LinearOrder K₂]

def lexLe [LinearOrder K₁] [LinearOrder K₂] (a b : K₂ × Key K₁ K₂) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance [LinearOrder K₁] [LinearOrder K₂] : DecidableRel (lexLe (K₁ := K₁) (K₂ := K₂)) :=
  λ a b ↦ by unfold lexLe; infer_instance

section Transfer

/-
TODO(REVIEW):
PAPER FIX? -> for each sender-recipient pair (s, r) ∈ K2 × K where s ̸= r
-/
def keysUneq (k₂ : K₂) (k : Key K₁ K₂) : Prop :=
  match k with
  | .inl _   => True
  | .inr k₂' => k₂ ≠ k₂' 

infix:50 " ≠ₖ " => keysUneq 

@[deprecated]
instance [DecidableEq K₂] : DecidablePred (Function.uncurry (keysUneq (K₁ := K₁) (K₂ := K₂))) :=
  λ keys ↦
    by unfold Function.uncurry keysUneq
       rcases keys with ⟨_, _ | _⟩ <;> infer_instance

instance {k₂ : K₂} {k : Key K₁ K₂} [DecidableEq K₂] : Decidable (k₂ ≠ₖ k) := by
  unfold keysUneq
  cases k <;> infer_instance

/-
Sort will behave.
-/
section SortNotNaughty

instance : IsTrans (K₂ × Key K₁ K₂) lexLe := by
  constructor; dsimp [lexLe]
  intros a b c h₁ h₂
  aesop (add safe forward le_trans) (add safe forward lt_trans) (config := {warnOnNonterminal := false})
  · have : ¬ Sum.inr val_2 < Sum.inl val_1 := by simp [(·<·), Key.lt]
    contradiction
  · have : ¬ Sum.inr val_1 < Sum.inl val := by simp [(·<·), Key.lt]
    contradiction

instance : IsAntisymm (K₂ × Key K₁ K₂) lexLe := by
  constructor; dsimp [lexLe]
  intros a b h₁ h₂
  aesop (add safe forward IsAntisymm.antisymm)

instance : IsTotal (K₂ × Key K₁ K₂) lexLe := by
  constructor; dsimp [lexLe]
  intros a b
  by_cases eq : a.1 = b.1
  · simp [eq]
    apply le_total
  · have : a.1 < b.1 ∨ b.1 < a.1 := by aesop
    rcases this with h | h <;> tauto

end SortNotNaughty

noncomputable def TransactionsInBlock_transfer [Finite K₁] [Finite K₂] [AddZeroClass V]
  (π : BalanceProof K₁ K₂ V C Pi)
  (b : { b : Block K₁ K₂ C Sigma V // b.isTransferBlock }) :
  List (Τ K₁ K₂ V) :=
  match h : b.1 with
  | .transfer _ _ commitment S _ =>
    /-
      Plumbing, ignore.
    -/
    have : Fintype K₁ := Fintype.ofFinite _; have : Fintype K₂ := Fintype.ofFinite _
    /-
      PAPER: for each sender-recipient pair (s, r) ∈ K2 × K where s ̸= r

      TODO(MY ESTEEMED SELF):
      -- (Set.univ |>.prod Set.univ).toFinset.filter (Function.uncurry keysUneq)
    -/
    let senderRecipient : Finset (K₂ × Key K₁ K₂) := { (k₂, k) | (k₂ : K₂) (k : Key K₁ K₂) (_h : k₂ ≠ₖ k) }
    let sorted : List (K₂ × Key K₁ K₂) := senderRecipient.sort lexLe
    /-
      PAPER:
      v = t(r), where ( , t) = π(C, s), if s ∈ S and π(C, s) ̸= ⊥
          ⊥,                            if s ∈ S and π(C, s) = ⊥
          0,                            if s /∈ S

      NB this is using the old notion of `Dict` because it's half a day's of work to restitch to the new one.
    -/
    let v (s : K₂) (r : Key K₁ K₂) : Option V :=
      if s ∉ S then .some 0 else 
      if h : (commitment, s) ∈ π.keys
      then let (_, _, t) := π[(commitment, s)]
           t.lookup r
      else .none
    sorted.map λ (s, r) ↦ (s, r, v s r)
  | .deposit .. | .withdrawal .. => by aesop

end Transfer

section Withdrawal

/--
TODO(REVIEW):
> Given a withdrawal block, the list of transactions extracted from it consists of
  a transaction from each L1 account to the source account in order:

In... what order?
-/
noncomputable def TransactionsInBlock_withdrawal [Finite K₁]
  (b : { b : Block K₁ K₂ C Sigma V // b.isWithdrawalBlock }) :
  List (Τ K₁ K₂ V) :=
  match h : b.1 with
  | .withdrawal withdrawals =>
    /-
      Plumbing. Ignore.
    -/
    have : Fintype K₁ := Fintype.ofFinite _

    /-
      The paper says 'in order'. This natural linear order?
    -/
    let k₁InOrder := { s | s : K₁ }.toFinset.sort (·≤·)
    k₁InOrder.map λ s : K₁ ↦ (s, .Source, withdrawals.lookup s)
    -- TODO(MY ESTEEMED SELF): This is of replication for l.map λ x ↦ (x, ...) happens in the transfer as well.
    -- Might be worth giving it a think to avoid reproving random stuff in the future.
  | .deposit r v | .transfer .. => by aesop

noncomputable def TransactionsInBlock [Finite K₁] [Finite K₂] [AddZeroClass V] 
  (π : BalanceProof K₁ K₂ V C Pi) (b : Block K₁ K₂ C Sigma V) : List (Τ K₁ K₂ V) := 
  match h : b with
  | .deposit ..    => TransactionsInBlock_deposit ⟨b, by simp only [h]⟩
  | .transfer ..   => TransactionsInBlock_transfer π ⟨b, by simp only [h]⟩
  | .withdrawal .. => TransactionsInBlock_withdrawal ⟨b, by simp only [h]⟩

noncomputable def TransactionsInBlocks [Finite K₁] [Finite K₂] [AddZeroClass V] 
  (π : BalanceProof K₁ K₂ V C Pi) (bs : List (Block K₁ K₂ C Sigma V)) : List (Τ K₁ K₂ V) :=
  (bs.map (TransactionsInBlock π)).join

end Withdrawal

end Order

end Extraction

/-
B.2 Step 2: Computing balances from a list of partial transactions
-/
section Computation

/--
TODO(MY ESTEEMED SELF): Is this horrible dependent type going to come bite me in the behind?
Let's find out!
-/
@[deprecated]
def S' [OfNat V 0] [LE V] := Finmap (λ (k : Kbar K₁ K₂) ↦ { v : V // k matches .Source ∨ 0 ≤ v })

/--
TODO(REVIEW):
PAPER FIX? -> In our case, a state is an assignment of a balance to each account, where every
non-source account has a positive balance:
                         ^^^^^^^^ - I am guessing nonnegative? PAPER FIX? 
-/
abbrev S (K₁ K₂ V : Type) [OfNat V 0] [LE V] := Kbar K₁ K₂ → V

def S.isValid [OfNat V 0] [LE V] (s : S K₁ K₂ V) :=
  ∀ k : Kbar K₁ K₂, k matches .Source ∨ 0 ≤ s k

instance [OfNat V 0] [LE V] : Finite (S K₁ K₂ V) := inferInstance 

/--
PAPER: where the set of transactions is the subset Tc ⊆ T, called the complete transactions
-/
abbrev Τc (K₁ K₂ V : Type) [OfNat V 0] [LE V] : Type := { τ : Τ K₁ K₂ V // τ.isComplete }

noncomputable def e (i : Kbar K₁ K₂) : Kbar K₁ K₂ → ℤ := λ j ↦ if i = j then 1 else 0

/-
We use the full lattice oredered ableian group structure with reckless abandon here.
There is technically still no need to for all the upcoming definitions
but we are at the core of the protocol and so might as well.
-/
section WithStructuredTypes

/-
TODO(REVIEW):
Given they're doing the big meet, I think the paper can say the lattice is complete, and implify [Finite V] anyway?
-/
variable [LinearOrder K₁]
         [LinearOrder K₂]
         [CompleteLattice V]
         [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

def v' (v : V) (b : S K₁ K₂ V) (s : Kbar K₁ K₂) : V :=
  match s with
  | .Source => v
  | .key _  => v ⊓ b s

/--
TODO(REVIEW):
The subtraction is simple - we can subtract integers in their additive group.
The scalar multiplication (·•·) comes initially from the underlying `SubNegMonoid`, i.e.
> A `SubNegMonoid` is an `AddMonoid` with unary `-` and binary `-` operations
> satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.
This is kinda of a Mathlib artifact they use, but it looks to me that this is really just the 'fundamental'
multiplication by scalar in an additive monoid, a'la `k * V` is `V + V + ... + V` k times.
So there's not super-deep analysis necessary here, I.. think???? - use `ℤ`'s 0 and 1 as 'the'
two special elements and abuse the fact that multiplcation by scalar here is repeated addition. Done.
Not sure what the best way to express this algebraically is but Lean seems to accept this just fine.

Of course, we can pretend that we have this `Module ℤ G`, because any additive commutative group `G` can be spooned into
it; cf. the `_removeLater` below as a sanity check, but I am not sure reasoning along these lines is necessary.
-/
noncomputable def fc (τc : Τc K₁ K₂ V) (b : S K₁ K₂ V) : S K₁ K₂ V :=
  have _removeLater : Module ℤ V := inferInstance
  λ k : Kbar K₁ K₂ ↦
    match τc with
    | ⟨⟨s, r, v⟩, hτ⟩ =>
      let v' := v' (v.get hτ.2) b s
      b k + (e r - e s) k • v'

/-
NB Lean's `Preorder` class has an addition requirement on how it expects `<` to be defined,
We'll use `False` stated as `a ≤ b ∧ ¬ b ≤ a`. Don't worry about it :).
-/
section Order

/--
PAPER: We first equip K2 with the discrete preorder.
-/
instance : LE (Kbar K₁ K₂) := ⟨(·=·)⟩

instance : Preorder (Kbar K₁ K₂) where
  le_refl := Eq.refl
  le_trans := λ _ _ _ ↦ Eq.trans

instance : Preorder (Kbar K₁ K₂ × Kbar K₁ K₂) := inferInstance

/--
PAPER: Then we equip V+ with the discrete preorder.
-/
instance (priority := high) : LE { v : V // 0 ≤ v } := ⟨(·=·)⟩
instance (priority := high) : LT { v : V // 0 ≤ v } := ⟨λ a b ↦ a ≤ b ∧ ¬ b ≤ a⟩ -- 😈

/--
High priority is imperative if we want Lean to pick this one up consistently.
Note that Lean already has `[Preorder α] (p : α → Prop) : Preorder (Subtype p)`, but we want ours.
-/
instance (priority := high) : Preorder { v : V // 0 ≤ v } where
  le_refl := Eq.refl
  le_trans := λ _ _ _ ↦ Eq.trans

/--
Definition 15
Let (X, ≤X) be a proset. We define the induced preorder ≤ on
Maybe(X) where for all x, y ∈ M aybe(X) we have
x ≤ y ⇔ x = ⊥ ∨ (x, y ∈ X ∧ x ≤X y)
-/
instance (priority := high) maybeInduced {α : Type} [Preorder α] : Preorder (Option α) :=
  let le : Option α → Option α → Prop := λ x y ↦
                                           match x, y with
                                           | .none, .none | .none, .some _ => True
                                           | .some x, .some y => x ≤ y
                                           | .some _, .none   => False
  {
    le := le
    lt := λ a b ↦ le a b ∧ ¬ le b a
    le_refl := by dsimp [le]; aesop
    le_trans := by dsimp [le, (·≤·)]; aesop (add safe forward le_trans)
  }

/--
PAPER: which induces a preorder on Maybe(V+)

NB this finds the custom high priority instance `maybeInduced`, i.e. Definition 15.
-/
instance : Preorder (Option { v : V // 0 ≤ v }) := inferInstance

/--
PAPER: We then get the induced product preorder on K2 × Maybe(V+).

NB the default behavviour is iso with the Definition 19. (cf. `Prod.mk_le_mk`)
-/
instance : Preorder (Kbar K₁ K₂ × Kbar K₁ K₂ × Option V) := inferInstance

/--
PAPER: and an induced subset preorder on the subset T

NB the default behaviour is iso with the Definition 18. (cf. `Preorder.lift`)
-/
instance : IsPreorder { τ : Τ K₁ K₂ V // τ.isValid } (·≤·) := inferInstance

/--
PAPER: we use the underlying preorder on V coming from the fact that V is a lattice

NB the default behaviour is the lattice-induced preorder. (cf. `PartialOrder.toPreorder`)
-/
instance : Preorder V := inferInstance

/--
PAPER: and give S the subset preorder

NB the default behaviour is iso with the Definition 18. (cf. `Preorder.lift`)
NB the default behaviour to find the preorder for the underlying function is iso with 
Definition 16. (cf. `Pi.le_def`)
-/
instance : Preorder { s : S K₁ K₂ V // s.isValid } := inferInstance

/--
PAPER: Given these preorders on T and S, we get an induced product preorder on T × S

NB the default behavviour is iso with the Definition 19. (cf. `Prod.mk_le_mk`)
-/
instance : Preorder ({ τ : Τ K₁ K₂ V // τ.isValid } × { s : S K₁ K₂ V // s.isValid }) := inferInstance

section Plumbing

/--
Noncomputable Fintype might seem strange but `Fintyp` fits better in Lean's hierarchy and removes
a bit of friction when converting to finset.

NB the current setup is such that this is unnecessary, will likely remove.
-/
@[deprecated]
noncomputable instance : Fintype (Τ K₁ K₂ V) := Fintype.ofFinite _
@[deprecated]
noncomputable instance : Fintype (Τc K₁ K₂ V) := Fintype.ofFinite _
@[deprecated]
noncomputable instance : Fintype { s : S K₁ K₂ V // s.isValid } := Fintype.ofFinite _

/--
And the obvious lift from `Τ.isComplete` to `Τ.isValid` to make Lean happy.
-/
instance : Coe (Τc K₁ K₂ V) { τ : Τ K₁ K₂ V // τ.isValid } := ⟨λ x ↦ ⟨x.1, x.2.1⟩⟩

end Plumbing

end Order

/--
NB might be subject to change, I'd rather prove the subset properties post facto, just want to make sure
that the orders we get here are appropriate.
-/
noncomputable def f (b : { s : S K₁ K₂ V // s.isValid })
                    (T : { τ : Τ K₁ K₂ V // τ.isValid }) : { s : S K₁ K₂ V // s.isValid } :=
  let univ := { (T', b') | (T' : Τc K₁ K₂ V) (b' : { s : S K₁ K₂ V // s.isValid }) (_h : (T, b) ≤ (↑T', b')) }
  ⟨⨅ x ∈ univ, fc x.1 x.2, sorry⟩

def S.initial (K₁ K₂ V : Type) [OfNat V 0] [LE V] : S K₁ K₂ V := λ _ ↦ 0

noncomputable def fStar (Ts : List { τ : Τ K₁ K₂ V // τ.isValid })
                        (s₀ : { s : S K₁ K₂ V // s.isValid }) : { s : S K₁ K₂ V // s.isValid } :=
  Ts.foldl f s₀

noncomputable def Bal (π : BalanceProof K₁ K₂ V C Pi) (bs : List (Block K₁ K₂ C Sigma V)) : { s : S K₁ K₂ V // s.isValid } :=
  have temporaryHole₁ : Τ K₁ K₂ V → { τ : Τ K₁ K₂ V // τ.isValid } := sorry
  have temporaryHole₂ : (S.initial K₁ K₂ V).isValid := sorry
  fStar ((TransactionsInBlocks π bs).map temporaryHole₁) ⟨S.initial K₁ K₂ V, temporaryHole₂⟩

end WithStructuredTypes

end Computation

end Balance

end Intmax
