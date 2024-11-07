import FVIntmax.Balance

namespace Intmax

open Mathlib

noncomputable section Lemma2

variable
  {Pi C Sigma : Type}
  {K₁ : Type} [Finite K₁]
  {K₂ : Type} [Finite K₂]
  {V : Type} [Lattice V] [AddCommGroup V]

-- /-
-- TODO(REVIEW): Why do we need this _here_?
-- -/
-- variable [AD : ADScheme K₂ (TransactionBatch K₁ K₂ V × K₂) C Pi]

/--
PAPER: First, we give VK+ the discrete preorder
-/
instance : Preorder (Key K₁ K₂ → V₊) := discretePreorder
-- instance {α ω : Type} [Preorder ω] : Preorder (Dict α ω) := by unfold Dict; infer_instance

omit [Finite K₁] [Finite K₂] in
/--
Demote a preorder on `Key K₁ K₂ → V₊` to equality ASAP.
-/
@[simp]
lemma discretePreorder_eq_equality_Key_Map_Vplus {a b : Key K₁ K₂ → V₊} : a ≤ b ↔ a = b := by
  simp only [LE.le]
  aesop

/--
NB: Actually we'll use the notion of 'transaction batch' here.
    We know that `TransactionBatch K₁ K₂ V` is by definition `Key K₁ K₂ → V₊`.
-/
instance : Preorder (TransactionBatch K₁ K₂ V) := discretePreorder

/--
Demote a preorder on `TransactionBatch` to equality ASAP.
-/
@[simp]
lemma discretePreorder_eq_equality_TransactionBatch {a b : TransactionBatch K₁ K₂ V} : a ≤ b ↔ a = b := by
  simp only [LE.le]
  aesop

/--
PAPER: Then, we give AD.Π × {0, 1} ∗ the trivial preorder
-/
instance : Preorder (Pi × ExtraDataT) := trivialPreorder

/--
Demote a preorder on `(Pi × ExtraDataT)` to equality ASAP.
-/
@[simp]
lemma discretePreorder_eq_equality_Pi_Prod_ExtraDataT {a b : (Pi × ExtraDataT)} : a ≤ b := by
  simp [(·≤·), Preorder.toLE, instPreorderProdExtraDataT, trivialPreorder]

/--
PAPER: Finally, we give (AD.Π × {0, 1}∗) × VK+ the induced product preorder
-/
instance : Preorder ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V) := inferInstance
instance : Preorder (BalanceProof K₁ K₂ C Pi V) := by unfold BalanceProof; infer_instance

variable {π π' : BalanceProof K₁ K₂ C Pi V} {k : C × K₂}

lemma mem_of_BalanceProof_le (h : π ≤ π') (h₁ : k ∈ π) : k ∈ π' := by
  specialize h k; simp [(·≤·)] at h
  aesop (add simp Dict.mem_iff_isSome)

lemma eq_of_BalanceProof_le (h : π ≤ π') (h₁ : k ∈ π) (h₂ : k ∈ π') :
  ((π k).get h₁).2 = ((π' k).get h₂).2 := by
  specialize h k; simp [(·≤·)] at h; rw [Dict.mem_iff_isSome] at h₁
  aesop (add simp Dict.mem_iff_isSome)

lemma notin_of_BalanceProof_le_notin (h : π ≤ π') (h₁ : k ∉ π') : k ∉ π := by
  specialize h k; simp [(·≤·)] at h
  aesop (add simp Dict.mem_iff_isSome)

/-
To follow the argument in the paper, one has to emulate the set-theoretical set-switching by
abusing the underlying DTT of Lean.

This entire section is not really worth the headache.
-/
section HicSuntDracones

variable [LinearOrder K₁] [LinearOrder K₂]

section HelperFunctionsToAppeaseLean

variable {π π' : BalanceProof K₁ K₂ C Pi V}

open Mathlib

private abbrev length_of_TransactionsInBlocks (bs : List (Block K₁ K₂ C Sigma V)) :
  { n : ℕ // n = (TransactionsInBlocks (Classical.arbitrary _ : BalanceProof K₁ K₂ C Pi V) bs).length } :=
  ⟨(TransactionsInBlocks (Classical.arbitrary _ : BalanceProof K₁ K₂ C Pi V) bs).length, rfl⟩

/-
A lot of DTT 'convincing' takes place in here, do feel encouraged to ignore this.
-/
open Lean.Elab.Tactic in
elab "blast" "with" h:ident i:(ident)? : tactic => do
  match i with
  | .none => evalTactic <| ← `(tactic| first | (simp_all [length_transactionsInBlocks _ $h])
                                             | (rcases length_of_TransactionsInBlocks _ with ⟨_, hw⟩
                                                rw [length_transactionsInBlocks (π₂ := $h)] at hw
                                                aesop))
  | .some i => evalTactic <| ← `(tactic| (simp [length_of_TransactionsInBlocks] at $i:ident
                                          rcases $i:ident with ⟨i, hi⟩
                                          rw [length_transactionsInBlocks (π₂ := $h)] at hi
                                          aesop))

/--
TransactionsInBlocksFixed is TransactionsInBlocks over fixed-length vectors.
-/
private def TransactionsInBlocksFixed (π : BalanceProof K₁ K₂ C Pi V) (bs : List (Block K₁ K₂ C Sigma V)) :
  Vector (Τ K₁ K₂ V) (length_of_TransactionsInBlocks (Pi := Pi) bs).1 :=
  ⟨TransactionsInBlocks π bs, by blast with π⟩

variable [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

/--
Bal' is Bal restated in terms of composition of two functions.
-/
private def Bal' (bs : List (Block K₁ K₂ C Sigma V)) : BalanceProof K₁ K₂ C Pi V → S K₁ K₂ V :=
  fStar (s₀ := S.initial K₁ K₂ V) ∘ TransactionsInBlocks (bs := bs)

/--
Bal' is really Bal.
-/
private lemma Bal'_eq_Bal : Bal' bs π = Bal π bs := rfl 

/--
fStarFixed is fStar over fixed-length vectors.
-/
private def fStarFixed {n : ℕ}
  (Ts : Vector (Τ K₁ K₂ V) n) (s₀ : S K₁ K₂ V) : S K₁ K₂ V :=
  fStar Ts.1 s₀

/--
BalFixed is Bal over fixed-length vectors.
-/
private def BalFixed (bs : List (Block K₁ K₂ C Sigma V)) : BalanceProof K₁ K₂ C Pi V → S K₁ K₂ V :=
  λ π ↦ fStarFixed (s₀ := S.initial K₁ K₂ V) (TransactionsInBlocksFixed π bs)

/--
BalFixed' is Bal' over fixed-length vectors.
-/
private def BalFixed' (bs : List (Block K₁ K₂ C Sigma V)) : BalanceProof K₁ K₂ C Pi V → S K₁ K₂ V :=
  fStarFixed (n := (length_of_TransactionsInBlocks (Pi := Pi) bs).1)
             (s₀ := S.initial K₁ K₂ V) ∘ TransactionsInBlocksFixed (Pi := Pi) (bs := bs)

/--
BalFixed is really BalFixed'.
-/
private lemma BalFixed_eq_BalFixed' : BalFixed bs π = BalFixed' bs π := rfl

end HelperFunctionsToAppeaseLean

/--
We reason about order of `n`-long vectors generated by `TransactionsInBlocksFixed` by
extensionally observing the underlying arbitrarily-sized lists for all indices `i < n`.
-/
lemma TransactionsInBlocksFixed_le_of_TransactionsInBlocks
  {π π' : BalanceProof K₁ K₂ C Pi V}
  {bs : List (Block K₁ K₂ C Sigma V)}
  (h : ∀ i : Fin (length_of_TransactionsInBlocks bs).1,
    (TransactionsInBlocks π bs)[i]'(by blast with π i) ≤
    (TransactionsInBlocks π' bs)[i]'(by blast with π' i)) :
  TransactionsInBlocksFixed π bs ≤ TransactionsInBlocksFixed π' bs := Vec.le_of_ext_le h

/--
PAPER: Notice first that we have (s, r) = (s′, r′), since by construction, we have that the
sender and recipient of the transaction at a given index in the list of partial
transactions extracted from a balance proof and block list is only determined
by the arrangement of the three block types in the block list.
-/
lemma senderReceiver_transactionsInBlocks {bs : List (Block K₁ K₂ C Sigma V)}
                                          {s r v} {s' r' v'} {eq₁ eq₂} {i}
  (h₀ : i < (TransactionsInBlocks π bs).length)
  (h₁ : (TransactionsInBlocks π bs)[i] = ⟨(s, r, v), eq₁⟩)
  (h₂ : (TransactionsInBlocks π' bs)[i]'(by blast with π) = ⟨(s', r', v'), eq₂⟩) :
  s = s' ∧ r = r' := by
  have eq₁ := sender_transactionsInBlocks (Sigma := Sigma) (bs := bs) π π'
  have eq₂ := receiver_transactionsInBlocks (Sigma := Sigma) (bs := bs) π π'
  simp [List.ext_get_iff, length_transactionsInBlocks π' π] at eq₁ eq₂
  specialize eq₁ i h₀ h₀; specialize eq₂ i h₀ h₀
  aesop

set_option maxHeartbeats 1000000 in
/--
Given our custom preorder structure, articulate how two transactions can differ.

NB this is an auxiliary technical result for `v_transactionsInBlocks`, which comes from the paper.
-/
private lemma delta_TransactionsInBlock_transfer
  {b : { b : Block K₁ K₂ C Sigma V // b.isTransferBlock }}
  {π₁ π₂ : BalanceProof K₁ K₂ C Pi V}
  (h : π₁ ≤ π₂) : 
  ∀ i : ℕ, (hlen : i < (TransactionsInBlock_transfer π₁ b).length) →
    (TransactionsInBlock_transfer π₁ b)[i]'hlen =
    (TransactionsInBlock_transfer π₂ b)[i]'(by rwa [length_TransactionsInBlock_transfer _ π₁]) ∨
    ((TransactionsInBlock_transfer π₁ b)[i]'hlen).1.2.2.isNone := λ i hi ↦ by
  unfold TransactionsInBlock_transfer
  rcases b with _ | ⟨_, _, C, S, _⟩ | _ <;> [aesop; dsimp; aesop]
  set l :=
    (Finset.sort (Key.lexLe (K₁ := K₁) (K₂ := K₂))
                 { (k₂, k) | (k₂ : K₂) (k : Key K₁ K₂) (_h : k₂ ≠ₖ k) }).attach with eq
  have : i < l.length := by rw [eq]; simp [TransactionsInBlock_transfer] at hi ⊢; exact hi
  simp_rw [←eq]
  let elem := (C, (l[i]'this).1.1)
  by_cases eq' : elem ∉ π₁ ∧ elem ∈ π₂
  · by_cases eq'' : (l[i]'this).1.1 ∈ S <;> simp [← Dict.mem_dict_iff_mem_keys, elem, eq', eq'']
  · rcases not_and_or.1 eq' with eq' | eq'
    · have h₁ : elem ∈ π₁ := by simp at eq'; exact eq'
      have := mem_of_BalanceProof_le h h₁; simp [← Dict.mem_dict_iff_mem_keys, h₁, this]
      have := eq_of_BalanceProof_le h h₁ this
      aesop
    · have := notin_of_BalanceProof_le_notin h eq'
      simp [← Dict.mem_dict_iff_mem_keys, eq', this]

/--
PAPER: Then, we realize that the only way the two transactions Ti and T′ i
can differ, is if they are both extracted from the same transfer block B, and if π′
contains a proof of the transaction from s in B, and π doesn’t. In this case, we have v = ⊥, so we
get ((s, r), v) ≤ ((s′, r′), v′).
-/
lemma v_transactionsInBlocks {Bstar : List (Block K₁ K₂ C Sigma V)}
                             {π π' : BalanceProof K₁ K₂ C Pi V}
                             {s r v v'} {eq₁ eq₂} {i}
  (h : π ≤ π')
  (h₀ : i < (TransactionsInBlocks π Bstar).length)
  (h₁ : (TransactionsInBlocks π Bstar)[i] = ⟨(s, r, v), eq₁⟩)
  (h₂ : (TransactionsInBlocks π' Bstar)[i]'(by blast with π) = ⟨(s, r, v'), eq₂⟩) :
  v ≤ v' := by
  unfold TransactionsInBlocks at h₁ h₂
  apply List.map_eq_project_triple at h₁
  apply List.map_eq_project_triple at h₂
  rw [←h₁, ←h₂]
  apply List.map_join_unnecessarily_specific (by ext x; simp; rw [length_transactionsInBlock])
  intros b i h₃
  unfold TransactionsInBlock
  match h' : b with
  | Block.transfer .. =>
    rcases delta_TransactionsInBlock_transfer (b := ⟨b, by aesop⟩) h i (by aesop) <;>
           [aesop; (simp [(·≤·)]; aesop)]
  | Block.deposit .. | Block.withdrawal .. => simp

theorem monotone_TransactionsInBlocksFixed {Bstar : List (Block K₁ K₂ C Sigma V)} :
  Monotone λ (π : BalanceProof K₁ K₂ C Pi V) ↦ TransactionsInBlocksFixed π Bstar := by
  intros π π' h
  dsimp
  apply TransactionsInBlocksFixed_le_of_TransactionsInBlocks; rintro ⟨i, hi⟩; simp
  generalize eq : (TransactionsInBlocks π Bstar)[i]'(by blast with π) = Tstar
  generalize eq' : (TransactionsInBlocks π' Bstar)[i]'(by clear eq; blast with π') = Tstar'
  rcases Tstar with ⟨⟨s, r, v⟩, h₁⟩
  rcases Tstar' with ⟨⟨s', r', v'⟩, h₂⟩
  obtain ⟨⟨⟩, ⟨⟩⟩ := senderReceiver_transactionsInBlocks _ eq eq'; simp
  exact v_transactionsInBlocks h _ eq eq'

end HicSuntDracones

variable {n : ℕ}
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

section Monotone

omit [Finite K₁] [Finite K₂]

variable {b₁ b₂ : S K₁ K₂ V}
         {T₁ T₂ : Τ K₁ K₂ V}
         {k : Kbar K₁ K₂}
         {v₁ v₂ : Vector (Τ K₁ K₂ V) n}

lemma monotone_f (h₁ : b₁ ≤ b₂) (h₂ : T₁ ≤ T₂) : f b₁ T₁ k ≤ f b₂ T₂ k := by
  obtain ⟨inf₁, -⟩ := f_IsGLB_of_V' (b := b₁) (T := T₁) (k := k)
  have inf₂ := f_IsGLB_of_V' (b := b₂) (T := T₂) (k := k)
  have := V'_sset_V'_of_le (k := k) h₁ h₂
  rw [le_isGLB_iff inf₂, mem_lowerBounds]
  aesop

set_option maxHeartbeats 400000 in
/--
A version of `monotone_fStarFixed` to induce over an accumulator for which `s₁ ≤ b₂` in the general case.

Cf. `monotone_fStarFixed` for semantics, as its the auxiliary we are particularly interested in.
-/
private theorem monotone_fStarFixed_aux (h : v₁ ≤ v₂) (h₂ : b₁ ≤ b₂) :
                                        v₁.1.foldl f b₁ ≤ v₂.1.foldl f b₂ := by
  rcases v₁ with ⟨l₁, len₁⟩
  rcases v₂ with ⟨l₂, len₂⟩
  induction' l₁ with hd₁ tl₁ ih generalizing b₁ b₂ l₂ n <;> rcases l₂ with _ | ⟨hd₂, tl₂⟩
  · exact h₂
  · simp at len₁ len₂; omega
  · simp at len₁ len₂; omega
  · rcases n with _ | n <;> [simp at len₁; skip]
    have := @Vec.le_cons _ _ _ _ _ _ _ (v₁ := ⟨hd₁ :: tl₁, len₁⟩) (v₂ := ⟨hd₂ :: tl₂, len₂⟩)
                         (by aesop) (by aesop) rfl rfl h
    have eq : f b₁ hd₁ ≤ f b₂ hd₂ := by
      dsimp [(·≤·)]; intros k
      have := monotone_f (k := k) h₂ this.1; aesop
    exact ih eq _ tl₂ _ this.2

lemma monotone_fStarFixed :
  Monotone λ (Ts : Vector (Τ K₁ K₂ V) n) ↦ Intmax.fStarFixed Ts (S.initial K₁ K₂ V) :=
  λ _ _ ↦ flip monotone_fStarFixed_aux (le_refl _)

end Monotone

variable [LinearOrder K₁] [LinearOrder K₂]
         {π₁ π₂ : BalanceProof K₁ K₂ C Pi V}
         {bs : List (Block K₁ K₂ C Sigma V)}

/--
PAPER: Lemma 2. The balance function Bal is monotone in its first argument 
-/
lemma lemma2 (h : π₁ ≤ π₂) : Bal π₁ bs ≤ Bal π₂ bs := by
  simp only [←Bal'_eq_Bal]
  suffices BalFixed bs π₁ ≤ BalFixed bs π₂ by aesop
  rw [BalFixed_eq_BalFixed', BalFixed_eq_BalFixed']
  exact Monotone.comp monotone_fStarFixed monotone_TransactionsInBlocksFixed h

end Lemma2

end Intmax
