import GMLInit.Data.Basic
import GMLInit.Data.Equiv
import GMLInit.Data.Nat
import GMLInit.Data.Option
import GMLInit.Logic.Relation

class Enum (α : Type _) where
  enum : Nat → Option α
  find : α → Nat
  spec (x : α) : enum (find x) = some x

namespace Enum

instance (α) [Enum α] : DecidableEq α
| x, y =>
  if h: find x = find y
  then
    Decidable.isTrue $ by
      apply Option.some.inj
      rw [←spec x, ←spec y, h]
  else
    Decidable.isFalse $ by
      intro h
      cases h
      contradiction

def ofEquiv (α β) [Enum α] (e : Equiv α β) : Enum β where
  enum n := (enum n).map e.fwd
  find x := find (e.rev x)
  spec x := by clean; simp [spec, Option.some_map, e.fwd_rev]

instance : Enum Empty where
  enum _ := none
  find x := nomatch x
  spec x := nomatch x

instance : Enum PUnit where
  enum
  | 0 => some PUnit.unit
  | _ => none
  find
  | PUnit.unit => 0
  spec
  | PUnit.unit => rfl

instance : Enum Bool where
  enum
  | 0 => some false
  | 1 => some true
  | _ => none
  find
  | false => 0
  | true => 1
  spec
  | false => rfl
  | true => rfl

instance : Enum Nat where
  enum n := some n
  find n := n
  spec n := rfl

instance (n) : Enum (Fin n) where
  enum m := if h : m < n then some ⟨m,h⟩ else none
  find | ⟨m,_⟩ => m
  spec | ⟨m,h⟩ => by simp [dif_pos h]

instance (α) [Enum α] : Enum (Option α) where
  enum
  | 0 => some none
  | n+1 => (enum n).map some
  find
  | none => 0
  | some x => find x + 1
  spec
  | none => rfl
  | some x => by
    clean
    split
    next => contradiction
    next h => cases h; simp [spec x]

instance (α β) [Enum α] [Enum β] : Enum (Sum α β) where
  enum n := if n.is_even then (enum n.half).map Sum.inl else (enum n.half).map Sum.inr
  find
  | Sum.inl x => (find x).inl
  | Sum.inr y => (find y).inr
  spec
  | Sum.inl x => by
    clean
    have : (find x).inl.is_even := by
      rw [Nat.is_even_inl]
    rw [if_pos this]
    rw [Nat.half_inl_eq]
    rw [spec]
    rw [Option.some_map]
  | Sum.inr y => by
    clean
    have : ¬ (find y).inr.is_even := by
      rw [←Nat.not_is_odd_eq_is_even]
      rw [Nat.is_odd_inr (find y)]
      exact Bool.noConfusion
    rw [if_neg this]
    rw [Nat.half_inr_eq]
    rw [spec]
    rw [Option.some_map]

instance (α β) [Enum α] [Enum β] : Enum (α × β) where
  enum n :=
    match enum n.fst, enum n.snd with
    | some x, some y => some (x,y)
    | _, _ => none
  find | (x,y) => Nat.pair (find x) (find y)
  spec | (x,y) => by simp [Nat.fst_pair, Nat.snd_pair, spec]

instance (α) (β : α → Type _) [Enum α] [(x : α) → Enum (β x)] : Enum ((x : α) × β x) where
  enum n :=
    match enum (α:=α) n.fst with
    | some x =>
      match enum (α:=β x) n.snd with
      | some y => some ⟨x, y⟩
      | none => none
    | none => none
  find | ⟨x,y⟩ => Nat.pair (find x) (find y)
  spec | ⟨x,y⟩ => by simp [Nat.fst_pair, Nat.snd_pair, spec]

instance (α) [Enum α] (p : α → Prop) [DecidablePred p] : Enum { x // p x } where
  enum n :=
    match enum n with
    | some x => if hx: p x then some ⟨x,hx⟩ else none
    | none => none
  find
  | ⟨x,_⟩ => find x
  spec
  | ⟨x,hx⟩ => by simp only [spec x, dif_pos hx]

section Quotient
variable {α} [Enum α] (s : Setoid α) [DecidableRel s.r]

private def enumQuot (n : Nat) : Option (Quotient s) :=
  match enum (α:=α) n with
  | none => none
  | some x => some (Quotient.mk s x)

private def matchQuot (x : α) (n : Nat) : Prop :=
  match enum (α:=α) n with
  | none => False
  | some y => Setoid.r x y

instance matchQuotDec (x : α) (n : Nat) : Decidable (matchQuot s x n) :=
  match h: enum (α:=α) n with
  | none =>
    Decidable.isFalse $ by
    unfold matchQuot
    rw [h]
    intro
    contradiction
  | some y =>
    if hxy : Setoid.r x y
    then Decidable.isTrue $ by
      unfold matchQuot
      rw [h]
      exact hxy
    else Decidable.isFalse $ by
      unfold matchQuot
      rw [h]
      exact hxy

private theorem matchQuotTotal (x : α) : ∃ n, matchQuot s x n := by
    exists find x
    unfold matchQuot
    rw [spec]
    clean
    reflexivity

private def findQuot (x : α) : Nat := Nat.find (matchQuot s x) (matchQuotTotal s x)

private theorem findQuotSound (x₁ x₂ : α) : Setoid.r x₁ x₂ → findQuot s x₁ = findQuot s x₂ := by
  intro h
  unfold findQuot
  apply Nat.find_ext
  intro n
  unfold matchQuot
  split
  next => reflexivity
  next =>
    constr
    · intro hx
      transitivity x₁
      · symmetry
        exact h
      · exact hx
    · intro hx
      transitivity x₂
      · exact h
      · exact hx

private theorem specQuot (x : α) : enumQuot s (findQuot s x) = some (Quotient.mk s x) := by
  unfold findQuot enumQuot
  split
  next h =>
    have hmatch : matchQuot s x (Nat.find (matchQuot s x) (matchQuotTotal s x)) := Nat.find_property (matchQuot s x)
    unfold matchQuot at hmatch h
    rw [h] at hmatch
    contradiction
  next y h =>
    have hmatch : matchQuot s x (Nat.find (matchQuot s x) (matchQuotTotal s x)) := Nat.find_property (matchQuot s x)
    unfold matchQuot at hmatch h
    simp [h] at hmatch
    rw [Quotient.sound hmatch]

instance instEnumQuot (α) [Enum α] (s : Setoid α) [DecidableRel s.r] : Enum (Quotient s) where
  enum := enumQuot s
  find := Quotient.lift (findQuot s) (findQuotSound s)
  spec := by
    intro x
    induction x using Quotient.ind
    apply specQuot

end Quotient

end Enum
