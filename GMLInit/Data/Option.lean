import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Meta.Basic

namespace Option

def get {α} : (a : Option α) → a.isSome → α
| some a, rfl => a

@[simp] lemma get_some (a : α) {h : (some a).isSome} : get (some a) h = a := rfl

@[simp] lemma none_map {α β} (f : α → β) : none.map f = none := rfl

@[simp] lemma some_map {α β} (f : α → β) (a : α) : (some a).map f = some (f a) := rfl

@[simp] lemma id_map {α} (a : Option α) : a.map id = a := by cases a <;> rfl

lemma comp_map {α β γ} (g : β → γ) (f : α → β) (a : Option α) : a.map (g ∘ f) = (a.map f).map g := by cases a <;> rfl

@[simp] lemma none_bind {α β} (f : α → Option β) : none.bind f = none := rfl

@[simp] lemma some_bind {α β} (f : α → Option β) (a : α) : (some a).bind f = f a := rfl

lemma bind_assoc {α β γ} (f : α → Option β) (g : β → Option γ) (a : Option α) : (a.bind f).bind g = a.bind (λ a => (f a).bind g) := by
  cases a with
  | none => rfl
  | some => rfl

def equiv {α β} (e : Equiv α β) : Equiv (Option α) (Option β) where
  fwd
  | some x => some (e.fwd x)
  | none => none
  rev
  | some x => some (e.rev x)
  | none => none
  spec := by
    intro
    | some _, some _ =>
      constr
      · intro | rfl => clean; rw [e.rev_fwd]
      · intro | rfl => clean; rw [e.fwd_rev]
    | some _, none => constr <;> (intro h; cases h)
    | none, some _ => constr <;> (intro h; cases h)
    | none, none => constr <;> intro | rfl => rfl

end Option
