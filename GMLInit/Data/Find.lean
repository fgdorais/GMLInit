import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Data.Index
import GMLInit.Data.Fin
import GMLInit.Data.Sigma

class Find (α : Sort _) where
  find? : (α → Bool) → Option α
  find_some {p : α → Bool} (x : α) : find? p = some x → p x = true
  find_none {p : α → Bool} (x : α) : find? p = none → p x = false

namespace Find

theorem findIsSome_iff_exists {α} [Find α] (p : α → Bool) : (find? p).isSome ↔ ∃ x, p x = true := by
  constr
  · match hp : find? p with
    | some x =>
      intro
      exists x
      exact find_some x hp
    | none =>
      intro
      contradiction
  · intro
    | ⟨x, hx⟩ =>
      match hp : find? p with
      | some _ =>
        rfl
      | none =>
        rw [find_none x hp] at hx
        contradiction

protected def ofEquiv {α β} [Find α] (e : Equiv α β) : Find β where
  find? p :=
    match find? (λ x => p (e.fwd x)) with
    | some x => some (e.fwd x)
    | none => none
  find_some := by
    intro p x h
    clean at h
    split at h
    next h' =>
      cases h
      apply find_some _ h'
    next =>
      contradiction
  find_none := by
    intro p x h
    clean at h
    split at h
    next =>
      contradiction
    next h' =>
      rw [←e.fwd_rev x]
      apply find_none _ h'

instance : Find Empty where
  find? _ := none
  find_some x h := by contradiction
  find_none x h := by cases x

instance : Find PUnit where
  find? p :=
    match p () with
    | true => some ()
    | false => none
  find_some
  | p, (), h => by
    clean at h
    split at h
    next => assumption
    next => contradiction
  find_none
  | p, (), h => by
    clean at h
    split at h
    next => contradiction
    next => assumption

instance : Find Bool where
  find? p :=
    match p true, p false with
    | true, _ => some true
    | _, true => some false
    | _, _ => none
  find_some
  | p, true, h => by
    clean at h
    split at h
    next => assumption
    next h => cases h
    next h => cases h
  | p, false, h => by
    clean at h
    split at h
    next h => cases h
    next => assumption
    next h => cases h
  find_none
  | p, true, h => by
    clean at h
    split at h
    next h => cases h
    next h => cases h
    next => rw [←Bool.not_eq_true]; assumption
  | p, false, h => by
    clean at h
    split at h
    next h => cases h
    next h => cases h
    next => rw [←Bool.not_eq_true]; assumption

instance (n) : Find (Fin n) where
  find? := Fin.find?
  find_some := Fin.find_some
  find_none := Fin.find_none

instance {α} (xs : List α) : Find (Index xs) where
  find? := Index.find?
  find_some := Index.find_some
  find_none := Index.find_none

instance [Find α] : Find (Option α) where
  find? p :=
    match p none with
    | true => some none
    | false => match find? (λ x => p (some x)) with
      | some x => some (some x)
      | none => none
  find_some
  | p, some x, h => by
    clean at h
    split at h;
    next h => cases h
    next h =>
      apply Find.find_some (p := λ x => p (some x))
      split at h
      next h => cases h; assumption
      next h => cases h
  | p, none, h => by
    clean at h
    split at h
    next => assumption
    next h =>
      split at h
      next h => cases h
      next h => cases h
  find_none
  | p, some x, h => by
    clean at h
    split at h
    next h => cases h
    next h =>
      split at h
      next h => cases h
      next =>
        apply find_none (p := λ x => p (some x))
        assumption
  | p, none, h => by
    clean at h
    split at h
    next h => cases h
    next h =>
      split at h
      next h => cases h
      next => assumption

instance (α β) [Find α] [Find β] : Find (Sum α β) where
  find? p :=
    match find? (λ x => p (Sum.inl x)), find? (λ y => p (Sum.inr y)) with
    | some x, _ => some (Sum.inl x)
    | _, some y => some (Sum.inr y)
    | _, _ => none
  find_some
  | p, Sum.inl x, h => by
    clean at h
    split at h
    next h =>
      cases h
      apply Find.find_some (p := λ x => p (Sum.inl x))
      assumption
    next h => cases h
    next h => cases h
  | p, Sum.inr y, h => by
    clean at h
    split at h
    next h => cases h
    next h =>
      cases h
      apply Find.find_some (p := λ y => p (Sum.inr y))
      assumption
    next h => cases h
  find_none
  | p, Sum.inl x, h => by
    clean at h
    split at h
    next => cases h
    next => cases h
    next _ h' =>
      apply Find.find_none (p := λ x => p (Sum.inl x))
      cases h: find? (λ x => p (Sum.inl x)) with
      | none => rfl
      | some x => absurd h' x; exact h
  | p, Sum.inr y, h => by
    clean at h
    split at h
    next h => cases h
    next h => cases h
    next h' _ =>
      apply Find.find_none (p := λ x => p (Sum.inr x))
      cases h: find? (λ x => p (Sum.inr x)) with
      | none => rfl
      | some x => absurd h' x; exact h

instance (α) [Find α] (C : α → Prop) [DecidablePred C] : Find { x : α // C x } where
  find? p :=
    match find? (λ x => if h: C x then p ⟨x,h⟩ else false) with
    | some x => if h: C x then some ⟨x,h⟩ else none
    | none => none
  find_some
  | p, ⟨x,hx⟩ => by
    intro h
    clean at h
    split at h
    next hsome =>
      have := find_some (p := λ x => if h: C x then p ⟨x,h⟩ else false) _ hsome
      split at h
      cases h
      next => simp [hx] at this; exact this
      next => contradiction
    next => contradiction
  find_none
  | p, ⟨x,hx⟩ => by
    intro h
    clean at h
    split at h
    next hsome =>
      have := find_some (p := λ x => if h: C x then p ⟨x,h⟩ else false) _ hsome
      split at h
      next => contradiction
      next hx' => simp [hx'] at this
    next hnone =>
      have := find_none (p := λ x => if h: C x then p ⟨x,h⟩ else false) x hnone
      simp [hx] at this
      exact this

instance (α) (β : α → Type _) [Find α] [(x : α) → Find (β x)] : Find ((x : α) × β x) where
  find? p :=
    match find? (λ x => Option.isSome (find? (λ y => p ⟨x,y⟩))) with
    | some x =>
      match find? (λ y => p ⟨x,y⟩) with
      | some y => some ⟨x,y⟩
      | none => none
    | none => none
  find_some
  | p, ⟨x,y⟩ => by
    intro h
    clean at h
    split at h
    next hsome₁ =>
      clean at h
      split at h
      next hsome₂ =>
        cases h
        apply find_some (p := λ y => p ⟨x,y⟩)
        exact hsome₂
      next => contradiction
    next => contradiction
  find_none
  | p, ⟨x,y⟩ => by
    intro h
    clean at h
    split at h
    next x' hsome₁ =>
      have := find_some _ hsome₁
      clean at h
      split at h
      next => contradiction
      next hnone₂ =>
        rw [hnone₂] at this
        contradiction
    next hnone₁ =>
      have := find_none x hnone₁
      apply find_none (p := λ y => p ⟨x,y⟩)
      cases hy: find? (λ y => p ⟨x,y⟩) with
      | none => rfl
      | some _ =>
        rw [hy] at this
        contradiction

instance (α β) [Find α] [Find β] : Find (α × β) :=
  Find.ofEquiv (Sigma.equivProd α β).inv

instance (α) (r : α → α → Prop) [Find α] : Find (Quot r) where
  find? p :=
    match find? (λ x => p (Quot.mk r x)) with
    | some x => some (Quot.mk r x)
    | none => none
  find_some
  | p, x, h => by
    induction x using Quot.ind with
    | mk x =>
      clean at h
      split at h
      next h =>
        injection h with h
        rw [←h]
        apply Find.find_some (p := λ x => p (Quot.mk r x))
        assumption
      next h => cases h
  find_none
  | p, x, h => by
    induction x using Quot.ind with
    | mk x =>
      clean at h
      split at h
      next h => cases h
      next h =>
        apply Find.find_none (p := λ x => p (Quot.mk r x))
        assumption

instance (α) (s : Setoid α) [Find α] : Find (Quotient s) :=
  inferInstanceAs (Find (Quot s.r))

end Find
