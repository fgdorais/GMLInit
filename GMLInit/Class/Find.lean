import GMLInit.Data.Equiv

class Find (α : Sort _) where
  find? : (α → Bool) → Option α
  find?_eq_some : find? p = some x → p x = true
  find?_eq_none : find? p = none → p x = false

namespace Find

theorem find_is_some_iff_exists_true {α} [Find α] (p : α → Bool) : (find? p).isSome ↔ ∃ x, p x = true := by
  constr
  · match hp : find? p with
    | some x =>
      intro
      exists x
      exact find?_eq_some hp
    | none =>
      intro
      contradiction
  · intro
    | ⟨x, hx⟩ =>
      match hp : find? p with
      | some _ =>
        rfl
      | none =>
        rw [find?_eq_none hp] at hx
        contradiction

theorem find_is_none_iff_forall_false {α} [Find α] (p : α → Bool) : (find? p).isNone ↔ ∀ x, p x = false := by
  constr
  · match hp : find? p with
    | some x =>
      intro _
      contradiction
    | none =>
      intro _ x
      exact find?_eq_none hp
  · intro h
    match hp : find? p with
    | some x =>
      absurd find?_eq_some hp
      rw [h]
      intro
      contradiction
    | none =>
      rfl

def instInhabited [Find α] [Nonempty α] : Inhabited α where
  default :=
    match h : find? (fun _ => true) with
    | some x => x
    | none => Bool.noConfusion $ show true = false by
      cases inferInstanceAs (Nonempty α) with
      | intro x => rw [←find?_eq_none (x:=x) h]

protected def ofEquiv {α β} [Find α] (e : Equiv α β) : Find β where
  find? p :=
    match find? fun x => p (e.fwd x) with
    | some x => some (e.fwd x)
    | none => none
  find?_eq_some := by
    intro p x h
    clean at h
    split at h
    next h' =>
      cases h
      apply find?_eq_some h'
    next =>
      contradiction
  find?_eq_none := by
    intro p x h
    clean at h
    split at h
    next =>
      contradiction
    next h' =>
      rw [←e.fwd_rev x]
      apply find?_eq_none h'

-- instance {α} (xs : List α) : Find (Index xs) where
--   find? := Index.find?
--   find?_eq_some := Index.find?_eq_some
--   find?_eq_none := Index.find?_eq_none

-- instance (α) [Finite α] : Find α :=
--   Find.ofEquiv (Finite.equivIndex α).inv

instance [Find α] : Find (Option α) where
  find? p :=
    match p none with
    | true => some none
    | false => match find? fun x => p (some x) with
      | some x => some (some x)
      | none => none
  find?_eq_some := by intro
    | p, some x, h =>
      clean at h
      split at h
      next => cases h
      next =>
        apply Find.find?_eq_some (p := fun x => p (some x))
        split at h
        next h => cases h; assumption
        next => cases h
    | p, none, h =>
      clean at h
      split at h
      next => assumption
      next =>
        split at h
        next => cases h
        next => cases h
  find?_eq_none := by intro
    | p, some x, h =>
      clean at h
      split at h
      next => cases h
      next =>
        split at h
        next => cases h
        next =>
          apply find?_eq_none (p := fun x => p (some x))
          assumption
    | p, none, h =>
      clean at h
      split at h
      next => cases h
      next h =>
        split at h
        next => cases h
        next => assumption

instance (α β) [Find α] [Find β] : Find (Sum α β) where
  find? p :=
    match find? fun x => p (Sum.inl x), find? fun y => p (Sum.inr y) with
    | some x, _ => some (Sum.inl x)
    | _, some y => some (Sum.inr y)
    | _, _ => none
  find?_eq_some := by intro
    | p, Sum.inl x, h =>
      clean at h
      split at h
      next =>
        cases h
        apply Find.find?_eq_some (p := fun x => p (Sum.inl x))
        assumption
      next => cases h
      next => cases h
    | p, Sum.inr y, h =>
      clean at h
      split at h
      next => cases h
      next =>
        cases h
        apply Find.find?_eq_some (p := fun y => p (Sum.inr y))
        assumption
      next h => cases h
  find?_eq_none := by intro
    | p, Sum.inl x, h =>
      clean at h
      split at h
      next => cases h
      next => cases h
      next h' _ =>
        apply Find.find?_eq_none (p := fun x => p (Sum.inl x))
        cases h: find? (fun x => p (Sum.inl x)) with
        | none => rfl
        | some x => absurd h' x; exact h
    | p, Sum.inr y, h =>
      clean at h
      split at h
      next => cases h
      next => cases h
      next _ h' =>
        apply Find.find?_eq_none (p := fun x => p (Sum.inr x))
        cases h: find? (fun x => p (Sum.inr x)) with
        | none => rfl
        | some x => absurd h' x; exact h

instance (α) [Find α] (C : α → Prop) [DecidablePred C] : Find { x : α // C x } where
  find? p :=
    match find? fun x => if h: C x then p ⟨x,h⟩ else false with
    | some x => if h: C x then some ⟨x,h⟩ else none
    | none => none
  find?_eq_some := by intro
    | p, ⟨x,hx⟩ =>
      intro h
      clean at h
      split at h
      next hsome =>
        have := find?_eq_some (p := fun x => if h: C x then p ⟨x,h⟩ else false) hsome
        split at h
        cases h
        next => simp [hx] at this; exact this
        next => contradiction
      next => contradiction
  find?_eq_none := by intro
    | p, ⟨x,hx⟩ =>
      intro h
      clean at h
      split at h
      next hsome =>
        have := find?_eq_some (p := fun x => if h: C x then p ⟨x,h⟩ else false) hsome
        split at h
        next => contradiction
        next hx' => simp [hx'] at this
      next hnone =>
        have := find?_eq_none (p := fun x => if h: C x then p ⟨x,h⟩ else false) (x:=x) hnone
        simp [hx] at this
        exact this

instance (α) (β : α → Type _) [Find α] [(x : α) → Find (β x)] : Find ((x : α) × β x) where
  find? p :=
    match find? fun x => Option.isSome (find? fun y => p ⟨x,y⟩) with
    | some x =>
      match find? fun y => p ⟨x,y⟩ with
      | some y => some ⟨x,y⟩
      | none => none
    | none => none
  find?_eq_some := by intro
    | p, ⟨x,y⟩ =>
      intro h
      clean at h
      split at h
      next hsome₁ =>
        split at h
        next hsome₂ =>
          cases h
          apply find?_eq_some (p := fun y => p ⟨x,y⟩)
          exact hsome₂
        next => contradiction
      next => contradiction
  find?_eq_none := by intro
    | p, ⟨x,y⟩ =>
      intro h
      clean at h
      split at h
      next x' hsome₁ =>
        have := find?_eq_some hsome₁
        split at h
        next => contradiction
        next hnone₂ =>
          rw [hnone₂] at this
          contradiction
      next hnone₁ =>
        have := find?_eq_none (x:=x) hnone₁
        apply find?_eq_none (p := fun y => p ⟨x,y⟩)
        cases hy: find? fun y => p ⟨x,y⟩ with
        | none => rfl
        | some _ =>
          rw [hy] at this
          contradiction

instance (α β) [Find α] [Find β] : Find (α × β) :=
  Find.ofEquiv (Sigma.equivProd α β).inv

instance (α) (r : α → α → Prop) [Find α] : Find (Quot r) where
  find? p :=
    match find? fun x => p (Quot.mk r x) with
    | some x => some (Quot.mk r x)
    | none => none
  find?_eq_some := by intro
    | p, x, h =>
      induction x using Quot.ind with
      | mk x =>
        clean at h
        split at h
        next =>
          injection h with h
          rw [←h]
          apply Find.find?_eq_some (p := fun x => p (Quot.mk r x))
          assumption
        next => cases h
  find?_eq_none := by intro
    | p, x, h =>
      induction x using Quot.ind with
      | mk x =>
        clean at h
        split at h
        next => cases h
        next =>
          apply Find.find?_eq_none (p := fun x => p (Quot.mk r x))
          assumption

instance (α) (s : Setoid α) [Find α] : Find (Quotient s) :=
  inferInstanceAs (Find (Quot s.r))

end Find

class WellOrd (α : Type _) extends Ord α where
  first? (p : α → Bool) : Option α
  first?_eq_none : first? p = none → p x = false
  first?_eq_some : first? p = some x → p x = true
  first?_is_min : first? p = some x → p y → compare y x ≠ .lt

namespace WellOrd

instance (α) [WellOrd α] : Find α where
  find? := first?
  find?_eq_none := first?_eq_none
  find?_eq_some := first?_eq_some

variable {α} [WellOrd α] [DecidableEq α]

instance : LE α := leOfOrd
instance : LT α := ltOfOrd

theorem lt_irrefl (x : α) : compare x x ≠ .lt := by
  match h : first? fun y => x = y with
  | some y =>
    have heq := first?_eq_some h
    have hge := first?_is_min h heq
    have heq := of_decide_eq_true heq
    rwa [←heq] at hge
  | none =>
    have hne := first?_eq_none h (x:=x)
    have hne := of_decide_eq_false hne
    absurd hne
    rfl

alias le_refl := lt_irrefl
