import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Meta.Basic

namespace Option

@[simp] lemma none_map {α β} (f : α → β) : none.map f = none := rfl

@[simp] lemma some_map {α β} (f : α → β) (a : α) : (some a).map f = some (f a) := rfl

@[simp] lemma id_map {α} (a : Option α) : a.map id = a := by
  cases a with
  | none => rfl
  | some => rfl

lemma comp_map {α β γ} (g : β → γ) (f : α → β) (a : Option α) : a.map (g ∘ f) = (a.map f).map g := by
  cases a with
  | none => rfl
  | some => rfl

@[simp] lemma none_bind {α β} (f : α → Option β) : none.bind f = none := rfl

@[simp] lemma some_bind {α β} (f : α → Option β) (a : α) : (some a).bind f = f a := rfl

lemma bind_assoc {α β γ} (f : α → Option β) (g : β → Option γ) (a : Option α) : (a.bind f).bind g = a.bind (λ a => (f a).bind g) := by
  cases a with
  | none => rfl
  | some => rfl

def equiv {α β} (e : Equiv α β) : Equiv (Option α) (Option β) where
  fwd := Option.map e.fwd
  rev := Option.map e.rev
  spec := by
    intros
    constr
    · intro h
      cases h
      rw [←comp_map, e.comp_rev_fwd, id_map]
    · intro h
      cases h
      rw [←comp_map, e.comp_fwd_rev, id_map]

end Option
