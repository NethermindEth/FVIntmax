import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finmap
import Mathlib.Data.Set.Image
import Mathlib.Logic.Embedding.Basic

namespace Intmax

section UniquelyIndexed

abbrev UniqueTokenT (α : Type) [Finite α] : Type := Fin (Finite.exists_equiv_fin α |>.choose)

abbrev UniquelyIndexed (α : Type) [Finite α] : Type := α ↪ UniqueTokenT α

namespace UniquelyIndexed

noncomputable def attach (α : Type) [Finite α] : UniquelyIndexed α :=
  have := Finite.exists_equiv_fin α
  this.choose_spec.some.toEmbedding

noncomputable instance {α : Type} [Finite α] : Inhabited (UniquelyIndexed α) := ⟨attach α⟩

@[simp]
lemma default_eq_attach (α : Type) [Finite α] : (default : UniquelyIndexed α) = attach α :=
  rfl

theorem injective {α : Type} [Finite α]
  (f : UniquelyIndexed α) : Function.Injective f := f.2

end UniquelyIndexed

end UniquelyIndexed

end Intmax

theorem List.keys_zipWith_sigma {l₁ : List α} {l₂ : List β}
  (h : l₁.length = l₂.length) : (List.zipWith Sigma.mk l₁ l₂).keys = l₁ := by
  induction l₁ generalizing l₂ with
  | nil => rfl
  | cons hd tl ih => rcases l₂ <;> aesop

namespace Multiset

section Multiset

variable {α : Type} {β : α → Type} {f : α → Sigma β} {m : Multiset α}

theorem keys_map_eq (h : ∀ x, Sigma.fst (f x) = x) : (Multiset.map f m).keys = m := by
  simp [Multiset.keys, h]

theorem nodup_map_of_pres_keys_nodup
  (h : ∀ x, Sigma.fst (f x) = x) (h₁ : m.Nodup) : (Multiset.map f m).Nodup := by
  rw [Multiset.nodup_map_iff_inj_on h₁]
  intros x _ y _ inj
  have h₁ := h x
  have h₂ := h y
  cc

theorem keys_dedup_map_pres_univ
  (h : m.Nodup) [DecidableEq (Sigma β)] (h₁ : ∀ x, Sigma.fst (f x) = x) :
  (Multiset.map f m).dedup.keys = m := by
  have : (Multiset.map f m).Nodup := nodup_map_of_pres_keys_nodup h₁ h
  rw [Multiset.dedup_eq_self.2 this, keys_map_eq h₁]

theorem nodup_filter_of_nodup [DecidableEq α] [DecidablePred P]
  (h : m.Nodup) : (Multiset.filter P m).Nodup := by
  rw [Multiset.nodup_iff_count_eq_one] at h ⊢
  intros x h₁
  rw [Multiset.count_filter]
  aesop

end Multiset

end Multiset
