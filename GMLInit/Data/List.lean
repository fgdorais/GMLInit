import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Meta.Basic

namespace List

@[simp] lemma nil_map {α β} (f : α → β) : [].map f = [] := rfl

@[simp] lemma cons_map {α β} (f : α → β) (a : α) (as : List α) : (a :: as).map f = f a :: as.map f := rfl

@[simp] lemma pure_map {α β} (f : α → β) (a : α) : [a].map f = [f a] := rfl

@[simp] lemma append_map {α β} (f : α → β) (as bs : List α) : (as ++ bs).map f = as.map f ++ bs.map f := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as H => rw [cons_append, cons_map, cons_map, cons_append, H]

@[simp] lemma id_map {α} (as : List α) : as.map id = as := by
  induction as with
  | nil => rfl
  | cons a as H => unfold map; rw [H]; rfl

lemma comp_map {α β γ} (g : β → γ) (f : α → β) (as : List α) : (as.map f).map g = as.map (g ∘ f) := by
  induction as with
  | nil => rfl
  | cons a as H => unfold map; rw [H]

@[simp] lemma nil_bind {α β} (f : α → List β) : [].bind f = [] := rfl

@[simp] lemma cons_bind {α β} (f : α → List β) (a : α) (as : List α) : (a :: as).bind f = f a ++ as.bind f := rfl

@[simp] lemma pure_bind {α β} (f : α → List β) (a : α) : [a].bind f = f a := by rw [cons_bind, nil_bind, append_nil]

@[simp] lemma append_bind {α β} (f : α → List β) (as bs : List α) : (as ++ bs).bind f = as.bind f ++ bs.bind f := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as H => rw [cons_append, cons_bind, cons_bind, append_assoc, H]

lemma bind_assoc {α β γ} (f : α → List β) (g : β → List γ) (as : List α) : (as.bind f).bind g = as.bind (λ a => (f a).bind g) := by
  induction as with
  | nil => rfl
  | cons a as H => rw [cons_bind, cons_bind, append_bind, H]

def equiv {α β} (e : Equiv α β) : Equiv (List α) (List β) where
  fwd := List.map e.fwd
  rev := List.map e.rev
  spec xs ys := by
    split
    intro h; rw [←h, comp_map, e.comp_rev_fwd, id_map]
    intro h; rw [←h, comp_map, e.comp_fwd_rev, id_map]

end List
