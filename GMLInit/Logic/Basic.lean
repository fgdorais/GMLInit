import GMLInit.Prelude

-- Stable Propositions --

class inductive Stable (a : Prop) : Prop
| protected intro : (¬¬a → a) → Stable a

abbrev inferStable (a : Prop) [inst : Stable a] := inst

protected def Stable.by_contradiction {a : Prop} [inst : Stable a] : ¬¬a → a :=
  match inst with | Stable.intro h => h

/-- double negation elimination (DNE) -/
theorem Stable.dne (a : Prop) [inst : Stable a] : ¬¬a → a :=
  match inst with | Stable.intro h => h

/-- Pierces's law -/
theorem Stable.pierce (a b : Prop) [Stable a] : ((a → b) → a) → a :=
  λ h => Stable.by_contradiction λ na => na (h λ ha => absurd ha na)

abbrev StablePred {α} (p : α → Prop) := (x : α) → Stable (p x)

abbrev StableRel {α β} (r : α → β → Prop) := (x : α) → (y : β) → Stable (r x y)

abbrev StableEq (α) := StableRel (@Eq α)

class inductive StableList : List Prop → Prop
| nil : StableList []
| cons {a as} : Stable a → StableList as → StableList (a :: as)

namespace StableList

instance : StableList [] := StableList.nil

instance (a as) [Stable a] [StableList as] : StableList (a :: as) :=
  StableList.cons inferInstance inferInstance

protected def head (a as) : [StableList (a :: as)] → Stable a
| StableList.cons inst _ => inst

protected def tail (a as) : [StableList (a :: as)] → StableList as
| StableList.cons _ inst => inst

end StableList

-- Complemented Propositions --

class inductive Complemented (a : Prop) : Prop
| isTrue : a → Complemented a
| isFalse : ¬a → Complemented a

abbrev inferComplemented (a : Prop) [inst : Complemented a] := inst

/-- eliminator for `Complemented` -/
protected def Complemented.by_cases (a : Prop) [inst : Complemented a] {motive : Prop} (isTrue : a → motive) (isFalse : ¬a → motive) : motive :=
  match inst with
  | .isTrue h => isTrue h
  | .isFalse h => isFalse h

/-- excluded middle (EM) -/
theorem Complemented.em (a : Prop) [Complemented a] : a ∨ ¬a := Complemented.by_cases a Or.inl Or.inr

abbrev ComplementedPred {α} (p : α → Prop) := (x : α) → Complemented (p x)

abbrev ComplementedRel {α β} (r : α → β → Prop) := (x : α) → (y : β) → Complemented (r x y)

abbrev ComplementedEq (α) := ComplementedRel (@Eq α)

class inductive ComplementedList : List Prop → Prop
| nil : ComplementedList []
| cons {a as} : Complemented a → ComplementedList as → ComplementedList (a :: as)

namespace ComplementedList

instance : ComplementedList [] := ComplementedList.nil

instance (a as) [Complemented a] [ComplementedList as] : ComplementedList (a :: as) :=
  ComplementedList.cons inferInstance inferInstance

protected def head (a as) : [ComplementedList (a :: as)] → Complemented a
| ComplementedList.cons inst _ => inst

protected def tail (a as) : [ComplementedList (a :: as)] → ComplementedList as
| ComplementedList.cons _ inst => inst

instance instMap {α} (a : α → Prop) [ComplementedPred a] : (xs : List α) → ComplementedList (xs.map a)
| [] => ComplementedList.nil
| x::xs => ComplementedList.cons inferInstance (instMap a xs)

end ComplementedList

instance (a : Prop) : [Complemented a] → Stable a
| Complemented.isTrue h => Stable.intro (λ _ => h)
| Complemented.isFalse h => Stable.intro (absurd h)

-- Decidable Propositions --

abbrev inferDecidable (a : Prop) [inst : Decidable a] := inst

class inductive DecidableList : List Prop → Type
| nil : DecidableList []
| cons {a as} : Decidable a → DecidableList as → DecidableList (a :: as)

namespace DecidableList

instance : DecidableList [] := DecidableList.nil

instance (a as) [Decidable a] [DecidableList as] : DecidableList (a :: as) :=
  DecidableList.cons inferInstance inferInstance

protected def head (a as) : [DecidableList (a :: as)] → Decidable a
| DecidableList.cons inst _ => inst

protected def tail (a as) : [DecidableList (a :: as)] → DecidableList as
| DecidableList.cons _ inst => inst

instance instMap {α} (a : α → Prop) [DecidablePred a] : (xs : List α) → DecidableList (xs.map a)
| [] => DecidableList.nil
| x::xs => DecidableList.cons inferInstance (instMap a xs)

end DecidableList

instance (a : Prop) : [Decidable a] → Complemented a
| Decidable.isTrue h => Complemented.isTrue h
| Decidable.isFalse h => Complemented.isFalse h

-- Weakly Complemented Propositions --

class inductive WeaklyComplemented (a : Prop) : Prop
| protected isFalse : ¬a → WeaklyComplemented a
| protected isIrrefutable : ¬¬a → WeaklyComplemented a

abbrev inferWeaklyComplemented (a : Prop) [inst : WeaklyComplemented a] := inst

/-- weak excluded middle (WEM) -/
theorem WeaklyComplemented.wem (a : Prop) : [WeaklyComplemented a] → ¬¬a ∨ ¬a
| WeaklyComplemented.isIrrefutable h => Or.inl h
| WeaklyComplemented.isFalse h => Or.inr h

abbrev WeaklyComplementedPred {α} (p : α → Prop) := (x : α) → WeaklyComplemented (p x)

abbrev WeaklyComplementedRel {α β} (r : α → β → Prop) := (x : α) → (y : β) → WeaklyComplemented (r x y)

abbrev WeaklyComplementedEq (α) := WeaklyComplementedRel (@Eq α)

class inductive WeaklyComplementedList : List Prop → Prop
| nil : WeaklyComplementedList []
| cons {a as} : WeaklyComplemented a → WeaklyComplementedList as → WeaklyComplementedList (a :: as)

namespace WeaklyComplementedList

instance : WeaklyComplementedList [] := WeaklyComplementedList.nil

instance (a as) [WeaklyComplemented a] [WeaklyComplementedList as] : WeaklyComplementedList (a :: as) :=
  WeaklyComplementedList.cons inferInstance inferInstance

protected def head (a as) : [WeaklyComplementedList (a :: as)] → WeaklyComplemented a
| WeaklyComplementedList.cons inst _ => inst

protected def tail (a as) : [WeaklyComplementedList (a :: as)] → WeaklyComplementedList as
| WeaklyComplementedList.cons _ inst => inst

instance instMap {α} (a : α → Prop) [WeaklyComplementedPred a] : (xs : List α) → WeaklyComplementedList (xs.map a)
| [] => WeaklyComplementedList.nil
| x::xs => WeaklyComplementedList.cons inferInstance (instMap a xs)

end WeaklyComplementedList

def complementedOfStableOfWeaklyComplemented (a : Prop) [Stable a] : [WeaklyComplemented a] → Complemented a
| WeaklyComplemented.isFalse h => Complemented.isFalse h
| WeaklyComplemented.isIrrefutable h => Complemented.isTrue (Stable.by_contradiction h)

instance (a : Prop) : [Complemented a] → WeaklyComplemented a
| Complemented.isTrue h => WeaklyComplemented.isIrrefutable (absurd h)
| Complemented.isFalse h => WeaklyComplemented.isFalse h

instance (a : Prop) : [WeaklyComplemented a] → Complemented (¬a)
| WeaklyComplemented.isFalse h => Complemented.isTrue h
| WeaklyComplemented.isIrrefutable h => Complemented.isFalse h

-- Weakly Decidable Propositions --

class inductive WeaklyDecidable (a : Prop) : Type
| protected isFalse : ¬a → WeaklyDecidable a
| protected isIrrefutable : ¬¬a → WeaklyDecidable a

abbrev inferWeaklyDecidable (a : Prop) [inst : WeaklyDecidable a] := inst

abbrev WeaklyDecidablePred {α} (p : α → Prop) := (x : α) → WeaklyDecidable (p x)

abbrev WeaklyDecidableRel {α β} (r : α → β → Prop) := (x : α) → (y : β) → WeaklyDecidable (r x y)

abbrev WeaklyDecidableEq (α) := WeaklyDecidableRel (@Eq α)

class inductive WeaklyDecidableList : List Prop → Type
| nil : WeaklyDecidableList []
| cons {a as} : WeaklyDecidable a → WeaklyDecidableList as → WeaklyDecidableList (a :: as)

namespace WeaklyDecidableList

instance : WeaklyDecidableList [] := WeaklyDecidableList.nil

instance (a as) [WeaklyDecidable a] [WeaklyDecidableList as] : WeaklyDecidableList (a :: as) :=
  WeaklyDecidableList.cons inferInstance inferInstance

protected def head (a as) : [WeaklyDecidableList (a :: as)] → WeaklyDecidable a
| WeaklyDecidableList.cons inst _ => inst

protected def tail (a as) : [WeaklyDecidableList (a :: as)] → WeaklyDecidableList as
| WeaklyDecidableList.cons _ inst => inst

instance instMap {α} (a : α → Prop) [WeaklyDecidablePred a] : (xs : List α) → WeaklyDecidableList (xs.map a)
| [] => WeaklyDecidableList.nil
| x::xs => WeaklyDecidableList.cons inferInstance (instMap a xs)

end WeaklyDecidableList

def decidableOfStableOfWeaklyDecidable (a : Prop) [Stable a] : [WeaklyDecidable a] → Decidable a
| WeaklyDecidable.isFalse h => Decidable.isFalse h
| WeaklyDecidable.isIrrefutable h => Decidable.isTrue (Stable.by_contradiction h)

instance (a : Prop) : [Decidable a] → WeaklyDecidable a
| Decidable.isTrue h => WeaklyDecidable.isIrrefutable (absurd h)
| Decidable.isFalse h => WeaklyDecidable.isFalse h

instance (a : Prop) : [WeaklyDecidable a] → Decidable (¬a)
| WeaklyDecidable.isFalse h => Decidable.isTrue h
| WeaklyDecidable.isIrrefutable h => Decidable.isFalse h
